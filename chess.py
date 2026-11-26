#!/usr/bin/env python3
"""
Pygame Chess  -  Normal / Blitz / Army / Military / 4 Player
Bots from ~100 to ~1500 Elo.   Install:  pip3 install pygame-ce    Run:  python3 chess_game.py
LAN play: challenge other players on the same network by IP address (all variants, TCP port 5555),
watch friends' games, and run single-elimination tournaments (Tournament button on the menu).
"""
import sys
import json
import queue
import socket
import time
import random
import threading
import textwrap
from collections import deque
import pygame

# ----------------------------------------------------------------------------
# Constants
# ----------------------------------------------------------------------------
PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING = 1, 2, 3, 4, 5, 6
LETTER = {PAWN: "", KNIGHT: "N", BISHOP: "B", ROOK: "R", QUEEN: "Q", KING: "K"}
GLYPH = {KING: "\u265a", QUEEN: "\u265b", ROOK: "\u265c",
         BISHOP: "\u265d", KNIGHT: "\u265e", PAWN: "\u265f"}
VALS = [0, 100, 320, 330, 500, 900, 0]
INF = 10 ** 7
MATE = 10 ** 6

KN_D = [(1, 2), (2, 1), (-1, 2), (-2, 1), (1, -2), (2, -1), (-1, -2), (-2, -1)]
ORTH = [(1, 0), (-1, 0), (0, 1), (0, -1)]
DIAG = [(1, 1), (1, -1), (-1, 1), (-1, -1)]
KG_D = ORTH + DIAG
CASTLE_RM = {0: "Q", 7: "K", 56: "q", 63: "k", 4: "KQ", 60: "kq"}

# elo -> (max depth, eval noise in centipawns, chance of a pure random move, seconds per move)
LEVELS = {
    100: (1, 350, 0.55, 0.5),
    300: (1, 250, 0.25, 0.5),
    500: (1, 150, 0.10, 0.5),
    700: (2, 130, 0.04, 1.0),
    900: (2, 80, 0.00, 1.5),
    1100: (2, 40, 0.00, 2.0),
    1300: (3, 20, 0.00, 2.5),
    1500: (5, 0, 0.00, 3.0),
}
# 4-player bots: elo -> (noise in points, random-move chance)
LEVELS4 = {100: (10, 0.6), 300: (7, 0.3), 500: (5, 0.1), 700: (3.5, 0.03),
           900: (2.5, 0), 1100: (1.6, 0), 1300: (1.0, 0), 1500: (0.5, 0)}
ELOS = sorted(LEVELS)


def roll_path(f, t, width):
    """Squares strictly between f and t on a straight rank / file (the squares a tank rolls over)."""
    fr, fc = divmod(f, width)
    tr, tc = divmod(t, width)
    step = ((tr > fr) - (tr < fr)) * width + ((tc > fc) - (tc < fc))
    out, s = [], f + step
    while s != t:
        out.append(s)
        s += step
    return out


# Promotion flags.  2P: 4=Queen 6=Rook 7=Bishop 8=Knight.   4P: 1=Queen 4=Rook 6=Bishop 7=Knight.
# (flag 5 is the ranged shot, flags >= 100 / >= 1000 are helicopter double jumps)
PROMO_KIND = {4: QUEEN, 6: ROOK, 7: BISHOP, 8: KNIGHT}
PROMO4 = {1: QUEEN, 4: ROOK, 6: BISHOP, 7: KNIGHT}
JET_HITS_OWN = False      # Jet blast only destroys ENEMY non-king pieces (True = also your own)
ARTILLERY_COOLDOWN = 3     # owner moves an artillery must wait between two shots
ARMY_VALS = [0, 110, 550, 1100, 800, 1000, 0]    # soldier, heli, artillery, tank, jet (engine values)


# ----------------------------------------------------------------------------
# Two-player board (Normal / Blitz / Military)
# ----------------------------------------------------------------------------
class Board:
    def __init__(self, variant="normal"):
        self.military = variant in ("military", "fullarmy")
        self.army = variant in ("army", "fullarmy")
        self.vals = ARMY_VALS if self.army else VALS
        self.cd = {}                      # artillery cooldowns {square: owner moves left} (never mutated in place)
        self.rows, self.cols = (10, 9) if self.military else (8, 8)
        self.sq = [0] * (self.rows * self.cols)
        self.turn = 1
        self.castle = frozenset()
        self.ep = -1
        self.halfmove = 0
        self.kings = {1: -1, -1: -1}
        self.history = []
        cr, cc = (self.rows - 1) / 2, (self.cols - 1) / 2
        self.cen = [-int((abs(i // self.cols - cr) + abs(i % self.cols - cc)) * 3)
                    for i in range(self.rows * self.cols)]
        self._setup()
        self.end_thr = 0
        self.end_thr = int(self._nonpawn() * 0.35)
        self.history.append(self.key())

    def _setup(self):
        cols, rows = self.cols, self.rows
        if self.military:
            layout = [[ROOK, ROOK, QUEEN, ROOK, KING, ROOK, QUEEN, ROOK, ROOK],
                      [BISHOP, KNIGHT, KNIGHT, BISHOP, KNIGHT, BISHOP, KNIGHT, KNIGHT, BISHOP],
                      [PAWN] * cols, [PAWN] * cols]
        else:
            layout = [[ROOK, KNIGHT, BISHOP, QUEEN, KING, BISHOP, KNIGHT, ROOK], [PAWN] * cols]
            self.castle = frozenset("KQkq")
        for r, row in enumerate(layout):
            for c, k in enumerate(row):
                self.sq[r * cols + c] = k
                self.sq[(rows - 1 - r) * cols + c] = -k
        for i, p in enumerate(self.sq):
            if abs(p) == KING:
                self.kings[1 if p > 0 else -1] = i

    def _nonpawn(self):
        return sum(self.vals[abs(p)] for p in self.sq if p and abs(p) not in (PAWN, KING))

    def copy(self):
        b = Board.__new__(Board)
        b.military, b.rows, b.cols = self.military, self.rows, self.cols
        b.army, b.vals = self.army, self.vals
        b.cd = self.cd
        b.sq = self.sq[:]
        b.turn, b.castle, b.ep, b.halfmove = self.turn, self.castle, self.ep, self.halfmove
        b.kings = dict(self.kings)
        b.history = []
        b.cen, b.end_thr = self.cen, self.end_thr
        return b

    def key(self):
        return hash((tuple(self.sq), self.turn, self.castle, self.ep, tuple(sorted(self.cd.items()))))

    # -- attacks -----------------------------------------------------------
    def attacked(self, s, by):
        sq, rows, cols = self.sq, self.rows, self.cols
        r, c = divmod(s, cols)
        pr = r - by
        if 0 <= pr < rows:
            for dc in (-1, 1):
                pc = c + dc
                if 0 <= pc < cols and sq[pr * cols + pc] == by * PAWN:
                    return True
        n = by * KNIGHT
        for dr, dc in KN_D:
            nr, nc = r + dr, c + dc
            if 0 <= nr < rows and 0 <= nc < cols and sq[nr * cols + nc] == n:
                return True
        k = by * KING
        for dr, dc in KG_D:
            nr, nc = r + dr, c + dc
            if 0 <= nr < rows and 0 <= nc < cols and sq[nr * cols + nc] == k:
                return True
        rk, bs, q = by * ROOK, by * BISHOP, by * QUEEN
        if self.army:                       # tanks roll over enemy pieces: only own pieces and kings stop them
            for dr, dc in ORTH:
                nr, nc = r + dr, c + dc
                seen = False
                while 0 <= nr < rows and 0 <= nc < cols:
                    v = sq[nr * cols + nc]
                    if v:
                        if v == rk or (v == q and not seen):
                            return True
                        if v * by > 0 or abs(v) == KING:
                            break
                        seen = True
                    nr += dr
                    nc += dc
            ray_sets = ((DIAG, bs),)
        else:
            ray_sets = ((ORTH, rk), (DIAG, bs))
        for dirs, a in ray_sets:
            for dr, dc in dirs:
                nr, nc = r + dr, c + dc
                while 0 <= nr < rows and 0 <= nc < cols:
                    v = sq[nr * cols + nc]
                    if v:
                        if v == a or v == q:
                            return True
                        break
                    nr += dr
                    nc += dc
        return False

    def in_check(self, color=None):
        color = color or self.turn
        return self.attacked(self.kings[color], -color)

    # -- move generation ---------------------------------------------------
    def pseudo(self, color, caps_only=False):
        sq, rows, cols = self.sq, self.rows, self.cols
        out = []
        ap = out.append
        for i in range(len(sq)):
            p = sq[i]
            if p * color <= 0:
                continue
            k = abs(p)
            r, c = divmod(i, cols)
            if k == PAWN:
                nr = r + color
                promo = 4 if (nr == rows - 1 if color == 1 else nr == 0) else 0
                base = nr * cols
                for dc in (-1, 1):
                    nc = c + dc
                    if 0 <= nc < cols:
                        t = base + nc
                        v = sq[t]
                        if v * color < 0:
                            ap((i, t, promo))
                        elif v == 0 and t == self.ep:
                            ap((i, t, 1))
                if self.army:                                   # soldier: shoot the piece ahead
                    v = sq[base + c]
                    if v * color < 0 and abs(v) != KING:
                        ap((i, base + c, 5))
                if not caps_only or promo:
                    t = base + c
                    if sq[t] == 0:
                        ap((i, t, promo))
                        if not self.military and r == (1 if color == 1 else rows - 2):
                            t2 = t + color * cols
                            if sq[t2] == 0:
                                ap((i, t2, 0))
            elif k == KNIGHT or k == KING:
                for dr, dc in (KN_D if k == KNIGHT else KG_D):
                    nr, nc = r + dr, c + dc
                    if 0 <= nr < rows and 0 <= nc < cols:
                        t = nr * cols + nc
                        v = sq[t]
                        if v * color < 0 or (v == 0 and not caps_only):
                            ap((i, t, 0))
                if k == KING and self.castle and not caps_only:
                    self._castles(i, color, ap)
                elif k == KNIGHT and self.army:
                    self._heli(i, color, caps_only, ap)
            else:
                dirs = ORTH if k == ROOK else DIAG if k == BISHOP else KG_D
                for dr, dc in dirs:
                    nr, nc = r + dr, c + dc
                    rolled = False
                    while 0 <= nr < rows and 0 <= nc < cols:
                        t = nr * cols + nc
                        v = sq[t]
                        if v == 0:
                            if rolled or not caps_only:
                                ap((i, t, 9 if rolled else 0))
                        else:
                            if v * color < 0:
                                ap((i, t, 9 if rolled else 0))
                                if self.army and k == ROOK and abs(v) != KING:   # tank keeps rolling
                                    rolled = True
                                    nr += dr
                                    nc += dc
                                    continue
                            break
                        nr += dr
                        nc += dc
        if self.army:                                           # artillery: hit any enemy non-king piece
            targets = None
            for i in range(len(sq)):
                if sq[i] == color * BISHOP and not self.cd.get(i):
                    if targets is None:
                        targets = [t for t in range(len(sq)) if sq[t] * color < 0 and abs(sq[t]) != KING]
                    for t in targets:
                        ap((i, t, 5))
        return out

    def _heli(self, i, color, caps_only, ap):
        sq, rows, cols = self.sq, self.rows, self.cols
        r, c = divmod(i, cols)
        for dr, dc in KN_D:
            vr, vc = r + dr, c + dc
            if not (0 <= vr < rows and 0 <= vc < cols):
                continue
            v = vr * cols + vc
            pv = sq[v]
            if pv * color > 0 or abs(pv) == KING:
                continue
            for er, ec in KN_D:
                wr, wc = vr + er, vc + ec
                if 0 <= wr < rows and 0 <= wc < cols:
                    w = wr * cols + wc
                    pw = sq[w]
                    if w == i:                         # out and back: only when the first landing captures
                        if pv != 0:
                            ap((i, w, 100 + v))
                        continue
                    if pw * color > 0 or abs(pw) == KING or (caps_only and pw == 0 and pv == 0):
                        continue
                    ap((i, w, 100 + v))

    def blast_squares(self, t, color):
        sq, rows, cols = self.sq, self.rows, self.cols
        r, c = divmod(t, cols)
        out = []
        for dr, dc in KG_D:
            nr, nc = r + dr, c + dc
            if 0 <= nr < rows and 0 <= nc < cols:
                n = nr * cols + nc
                v = sq[n]
                if v and abs(v) != KING and (JET_HITS_OWN or v * color < 0):
                    out.append(n)
        return out

    def _castles(self, i, color, ap):
        sq = self.sq
        home = 4 if color == 1 else 60
        if i != home or self.attacked(i, -color):
            return
        ks, qs = ("K", "Q") if color == 1 else ("k", "q")
        if ks in self.castle and sq[i + 1] == 0 and sq[i + 2] == 0 and sq[i + 3] == color * ROOK \
                and not self.attacked(i + 1, -color) and not self.attacked(i + 2, -color):
            ap((i, i + 2, 2))
        if qs in self.castle and sq[i - 1] == 0 and sq[i - 2] == 0 and sq[i - 3] == 0 \
                and sq[i - 4] == color * ROOK \
                and not self.attacked(i - 1, -color) and not self.attacked(i - 2, -color):
            ap((i, i - 2, 3))

    def _tick(self, color):
        """The mover's artillery cooldowns drop by one on each of the owner's moves."""
        new = {}
        for s, n in self.cd.items():
            if self.sq[s] * color > 0:
                n -= 1
            if n > 0:
                new[s] = n
        return new

    def make(self, m):
        f, t, fl = m
        sq, cols = self.sq, self.cols
        p = sq[f]
        cap = sq[t] if t != f else 0
        color = 1 if p > 0 else -1
        old_c, old_ep, old_h = self.castle, self.ep, self.halfmove
        old_cd = self.cd
        ticked = self._tick(color) if old_cd else {}
        extra = None
        self.ep = -1
        if fl == 5:                                    # ranged shot: the shooter stays put
            sq[t] = 0
            touched = (t,)
        else:
            sq[f] = 0
            sq[t] = p
            if fl == 1:
                cs = t - color * cols
                cap = sq[cs]
                sq[cs] = 0
            elif fl in PROMO_KIND:
                sq[t] = PROMO_KIND[fl] * color
            elif fl == 2:
                sq[f + 1] = sq[f + 3]
                sq[f + 3] = 0
            elif fl == 3:
                sq[f - 1] = sq[f - 4]
                sq[f - 4] = 0
            elif fl == 9:                              # tank: crushes every piece it rolls over
                extra = [(n, sq[n]) for n in roll_path(f, t, cols) if sq[n]]
                for n, _ in extra:
                    sq[n] = 0
            elif fl >= 100:                            # helicopter: first jump landed on `via`
                v = fl - 100
                if sq[v]:
                    extra = [(v, sq[v])]
                    sq[v] = 0
            if self.army and cap and (p == QUEEN or p == -QUEEN):      # jet blast
                bl = self.blast_squares(t, color)
                if bl:
                    extra = (extra or []) + [(n, sq[n]) for n in bl]
                    for n in bl:
                        sq[n] = 0
            touched = (f, t)
            k = abs(p)
            if k == PAWN and abs(t - f) == 2 * cols:
                self.ep = (f + t) // 2
            elif k == KING:
                self.kings[color] = t
        if self.castle:
            rm = "".join(CASTLE_RM.get(x, "") for x in touched)
            if extra:
                rm += "".join(CASTLE_RM.get(n, "") for n, _ in extra)
            if rm:
                self.castle = frozenset(x for x in self.castle if x not in rm)
        self.halfmove = 0 if (abs(p) == PAWN or cap or extra or fl == 5) else self.halfmove + 1
        self.turn = -color
        if old_cd or (fl == 5 and abs(p) == BISHOP):
            new = ticked
            new.pop(t, None)                           # a destroyed piece takes its cooldown with it
            for n2, _ in (extra or ()):
                new.pop(n2, None)
            if fl == 5:
                if abs(p) == BISHOP:
                    new[f] = ARTILLERY_COOLDOWN        # artillery just fired
            elif f in new:
                new[t] = new.pop(f)                    # the cooldown travels with the artillery
            self.cd = new
        return ((f, t, fl), p, cap, old_c, old_ep, old_h, extra, old_cd)

    def unmake(self, u):
        (f, t, fl), p, cap, oc, oep, oh, extra, ocd = u
        self.cd = ocd
        sq, cols = self.sq, self.cols
        color = 1 if p > 0 else -1
        sq[f] = p
        if fl == 1:
            sq[t] = 0
            sq[t - color * cols] = cap
        elif t != f:
            sq[t] = cap
        if fl == 2:
            sq[f + 3] = sq[f + 1]
            sq[f + 1] = 0
        elif fl == 3:
            sq[f - 4] = sq[f - 1]
            sq[f - 1] = 0
        if extra:
            for n, v in extra:
                sq[n] = v
        if abs(p) == KING:
            self.kings[color] = f
        self.castle, self.ep, self.halfmove, self.turn = oc, oep, oh, color

    def legal(self):
        color = self.turn
        res = []
        for m in self.pseudo(color):
            u = self.make(m)
            if not self.attacked(self.kings[color], -color):
                res.append(m)
            self.unmake(u)
        return res

    def order(self, moves):
        sq, VALS = self.sq, self.vals

        def key(m):
            v = sq[m[1]]
            s = 10 * VALS[abs(v)] - VALS[abs(sq[m[0]])] // 10 if v else 0
            if m[2] == 4:
                s += 800
            elif m[2] == 1:
                s += 100
            elif m[2] == 9:
                s += 400
            return -s
        moves.sort(key=key)

    # -- evaluation (centipawns, white positive) ----------------------------
    def evaluate(self):
        sq, cols, rows, cen = self.sq, self.cols, self.rows, self.cen
        VALS = self.vals
        s = 0
        npm = 0
        for i, p in enumerate(sq):
            if p == 0:
                continue
            k = p if p > 0 else -p
            v = VALS[k]
            if k > 1 and k < 6:
                npm += v
            if k == PAWN:
                r = i // cols
                v += (r if p > 0 else rows - 1 - r) * 7 + cen[i] // 2
            elif k == KNIGHT or k == BISHOP:
                v += cen[i]
            s += v if p > 0 else -v
        endgame = npm < self.end_thr * 2
        for color in (1, -1):
            ki = self.kings[color]
            r = ki // cols
            home = r if color == 1 else rows - 1 - r
            kv = cen[ki] * 3 if endgame else -home * 12
            s += kv if color == 1 else -kv
        if endgame and abs(s) > 250:
            # mop-up: drive the losing king to the edge, bring the winner's king closer
            win = 1 if s > 0 else -1
            wk, lk = self.kings[win], self.kings[-win]
            dist = abs(wk // cols - lk // cols) + abs(wk % cols - lk % cols)
            bonus = -cen[lk] * 2 + (cols + rows - dist) * 4
            s += bonus * win
        return s

    # -- game state --------------------------------------------------------
    def insufficient(self):
        if self.army:
            return all(abs(p) == KING for p in self.sq if p)
        minors = 0
        for p in self.sq:
            k = abs(p)
            if k in (PAWN, ROOK, QUEEN):
                return False
            if k in (KNIGHT, BISHOP):
                minors += 1
        return minors <= 1


# ----------------------------------------------------------------------------
# Search
# ----------------------------------------------------------------------------
class Timeout(Exception):
    pass


class Ctx:
    def __init__(self):
        self.nodes = 0
        self.deadline = float("inf")


def qsearch(b, alpha, beta, ctx, qd):
    ctx.nodes += 1
    if ctx.nodes & 1023 == 0 and time.time() > ctx.deadline:
        raise Timeout
    color = b.turn
    stand = b.evaluate() * color
    if stand >= beta:
        return stand
    if stand > alpha:
        alpha = stand
    if qd <= 0:
        return stand
    moves = b.pseudo(color, caps_only=True)
    b.order(moves)
    if b.army:                       # artillery can hit anything: only look at the most promising captures
        moves = moves[:8]
    for m in moves:
        u = b.make(m)
        if b.attacked(b.kings[color], -color):
            b.unmake(u)
            continue
        s = -qsearch(b, -beta, -alpha, ctx, qd - 1)
        b.unmake(u)
        if s >= beta:
            return s
        if s > alpha:
            alpha = s
    return alpha


def negamax(b, depth, alpha, beta, ply, ctx):
    if depth <= 0:
        return qsearch(b, alpha, beta, ctx, 2 if b.army else 4)
    ctx.nodes += 1
    if ctx.nodes & 1023 == 0 and time.time() > ctx.deadline:
        raise Timeout
    color = b.turn
    moves = b.pseudo(color)
    b.order(moves)
    best = -INF
    legal = 0
    for m in moves:
        u = b.make(m)
        if b.attacked(b.kings[color], -color):
            b.unmake(u)
            continue
        legal += 1
        s = -negamax(b, depth - 1, -beta, -alpha, ply + 1, ctx)
        b.unmake(u)
        if s > best:
            best = s
        if best > alpha:
            alpha = best
        if alpha >= beta:
            break
    if legal == 0:
        return -MATE + ply if b.attacked(b.kings[color], -color) else 0
    return best


def choose_move(b, elo, tlimit):
    depth_max, noise, rand_p, _ = LEVELS[elo]
    legal = b.legal()
    if not legal:
        return None
    if len(legal) == 1:
        return legal[0]
    if random.random() < rand_p:
        return random.choice(legal)
    random.shuffle(legal)
    b.order(legal)
    color = b.turn
    quick = []                                   # static look at every move: fallback if the search runs out of time
    for m in legal:
        u = b.make(m)
        quick.append((b.evaluate() * color, m))
        b.unmake(u)
    ctx = Ctx()
    end = time.time() + tlimit
    result = None
    for d in range(1, depth_max + 1):
        ctx.deadline = end
        res = []
        try:
            alpha = -INF
            for m in legal:
                u = b.make(m)
                if noise:
                    s = -negamax(b, d - 1, -INF, INF, 1, ctx)
                else:
                    s = -negamax(b, d - 1, -INF, -alpha, 1, ctx)
                b.unmake(u)
                res.append((s, m))
                if s > alpha:
                    alpha = s
        except Timeout:
            if d == 1:                           # keep what was searched, static scores for the rest
                done = {mv for _, mv in res}
                result = res + [q for q in quick if q[1] not in done]
            break
        result = res
        if time.time() > end or abs(alpha) > MATE - 100:
            break
        legal = [m for s, m in sorted(result, key=lambda x: -x[0])]
    if not result:
        return legal[0]
    if noise:
        return max(result, key=lambda x: x[0] + random.gauss(0, noise))[1]
    return max(result, key=lambda x: x[0])[1]


# ----------------------------------------------------------------------------
# Four-player board (chess.com style FFA: standard 14x14, or Military 17x17)
# ----------------------------------------------------------------------------
PLAYER_NAMES = ["Red", "Blue", "Yellow", "Green"]
PLAYER_COLORS = [(214, 60, 60), (62, 108, 226), (232, 196, 36), (56, 168, 78)]
DEAD_COLOR = (128, 128, 128)
FDIRS = [(1, 0), (0, 1), (-1, 0), (0, -1)]          # pawn forward direction per player
SIDE = [(0, 1), (-1, 0), (0, -1), (1, 0)]           # direction from each king to its short-side rook
POINTS = {PAWN: 1, KNIGHT: 3, BISHOP: 5, ROOK: 5, QUEEN: 9, KING: 0}
SAFE_V = {PAWN: 1, KNIGHT: 3, BISHOP: 3.2, ROOK: 5, QUEEN: 9, KING: 0}
NOCAP_LIMIT = 160       # plies without a capture before the game is scored
PIECE_NAME = {PAWN: "pawn", KNIGHT: "knight", BISHOP: "bishop", ROOK: "rook", QUEEN: "queen", KING: "king"}

# Army variants: unit name + 3 letter tag drawn on the piece.
# EDIT THIS TABLE to match the units from the video. Only "Soldier = pawn" is confirmed;
# the others are placeholders that move exactly like the chess piece they replace.
ARMY_UNITS = {
    PAWN: ("Soldier", "SOL", "shoots piece ahead"),
    KNIGHT: ("Helicopter", "HEL", "2 jumps per turn"),
    BISHOP: ("Artillery", "ART", "shoots any piece, CD 3"),
    ROOK: ("Tank", "TNK", "rolls over enemies"),
    QUEEN: ("Fighter Jet", "JET", "blast radius 1"),
    KING: ("Commander", "CMD", ""),
}


class Board4:
    def __init__(self, layout="standard", army=False, teams=False):
        self.layout = layout
        self.army = army
        self.teams = teams                 # 2v2: Red + Yellow against Blue + Green
        self.hostile = [[o != p and (not teams or o % 2 != p % 2) for o in range(4)] for p in range(4)]
        self.cd = {}
        self.N, self.cut = (17, 4) if layout == "military" else (14, 3)
        N, cut = self.N, self.cut
        self.ok = [not ((r < cut or r > N - 1 - cut) and (c < cut or c > N - 1 - cut))
                   for r in range(N) for c in range(N)]
        self.sq = [None] * (N * N)
        self.alive = [True] * 4
        self.score = [0] * 4
        self.kings = [-1] * 4
        self.turn = 0
        self.since_cap = 0
        self.dbl = layout == "standard"                      # pawn double step
        if layout == "military":
            rows = [[ROOK, ROOK, QUEEN, ROOK, KING, ROOK, QUEEN, ROOK, ROOK],
                    [BISHOP, KNIGHT, KNIGHT, BISHOP, KNIGHT, BISHOP, KNIGHT, KNIGHT, BISHOP],
                    [PAWN] * 9, [PAWN] * 9]
        else:
            rows = [[ROOK, KNIGHT, BISHOP, QUEEN, KING, BISHOP, KNIGHT, ROOK], [PAWN] * 8]
        for p in range(4):
            for r, row in enumerate(rows):
                for c, k in enumerate(row):
                    rr, cc = r, cut + c
                    for _ in range(p):                      # rotate clockwise 90 degrees per seat
                        rr, cc = N - 1 - cc, rr
                    self.sq[rr * N + cc] = (p, k)
                    if k == KING:
                        self.kings[p] = rr * N + cc
        # castling (standard layout only)
        self.step = [d[0] * N + d[1] for d in SIDE]
        self.king_home = list(self.kings)
        self.rook_home = {}
        self.cr = tuple(frozenset() for _ in range(4))
        if layout == "standard":
            self.cr = tuple(frozenset("KQ") for _ in range(4))
            for p in range(4):
                s, ki = self.step[p], self.kings[p]
                self.rook_home[ki + 3 * s] = (p, "K")
                self.rook_home[ki - 4 * s] = (p, "Q")

    def foes(self, p):
        """foes(p)[o] is True when player p may capture / attack pieces owned by o (dead pieces are fair game)."""
        h, al = self.hostile[p], self.alive
        return [h[o] or (o != p and not al[o]) for o in range(4)]

    def is_foe(self, p, x):
        o = x[0]
        return o != p and (self.hostile[p][o] or not self.alive[o])

    def over(self):
        al = self.alive
        if sum(al) <= 1:
            return True
        return self.teams and (not (al[0] or al[2]) or not (al[1] or al[3]))

    def is_promo(self, p, r, c):
        e = self.N - 1 - self.cut
        return (r == e, c == e, r == self.cut, c == self.cut)[p]

    def on_start(self, p, r, c):
        e = self.N - 2
        return (r == 1, c == 1, r == e, c == e)[p]

    def pseudo(self, p):
        hs = self.foes(p)
        sq, ok, N = self.sq, self.ok, self.N
        out = []
        ap = out.append
        for i in range(N * N):
            pc = sq[i]
            if pc is None or pc[0] != p:
                continue
            k = pc[1]
            r, c = divmod(i, N)
            if k == PAWN:
                dr, dc = FDIRS[p]
                nr, nc = r + dr, c + dc
                if self.army and 0 <= nr < N and 0 <= nc < N and ok[nr * N + nc]:      # soldier shot
                    x = sq[nr * N + nc]
                    if x is not None and hs[x[0]] and x[1] != KING:
                        ap((i, nr * N + nc, 5))
                if 0 <= nr < N and 0 <= nc < N and ok[nr * N + nc] and sq[nr * N + nc] is None:
                    ap((i, nr * N + nc, 1 if self.is_promo(p, nr, nc) else 0))
                    if self.dbl and self.on_start(p, r, c):
                        r2, c2 = nr + dr, nc + dc
                        if ok[r2 * N + c2] and sq[r2 * N + c2] is None:
                            ap((i, r2 * N + c2, 0))
                perps = ((0, -1), (0, 1)) if dr else ((-1, 0), (1, 0))
                for pr_, pc_ in perps:
                    nr, nc = r + dr + pr_, c + dc + pc_
                    if 0 <= nr < N and 0 <= nc < N and ok[nr * N + nc]:
                        x = sq[nr * N + nc]
                        if x is not None and hs[x[0]] and x[1] != KING:
                            ap((i, nr * N + nc, 1 if self.is_promo(p, nr, nc) else 0))
            elif k == KNIGHT or k == KING:
                for dr, dc in (KN_D if k == KNIGHT else KG_D):
                    nr, nc = r + dr, c + dc
                    if 0 <= nr < N and 0 <= nc < N and ok[nr * N + nc]:
                        x = sq[nr * N + nc]
                        if x is None or (hs[x[0]] and x[1] != KING):
                            ap((i, nr * N + nc, 0))
                if k == KING and self.cr[p] and i == self.king_home[p]:
                    self._castles(i, p, ap)
                elif k == KNIGHT and self.army:
                    self._heli(i, p, ap)
            else:
                dirs = ORTH if k == ROOK else DIAG if k == BISHOP else KG_D
                for dr, dc in dirs:
                    nr, nc = r + dr, c + dc
                    rolled = False
                    while 0 <= nr < N and 0 <= nc < N and ok[nr * N + nc]:
                        x = sq[nr * N + nc]
                        if x is None:
                            ap((i, nr * N + nc, 9 if rolled else 0))
                        else:
                            if hs[x[0]] and x[1] != KING:
                                ap((i, nr * N + nc, 9 if rolled else 0))
                                if self.army and k == ROOK:                  # tank keeps rolling
                                    rolled = True
                                    nr += dr
                                    nc += dc
                                    continue
                            break
                        nr += dr
                        nc += dc
        if self.army:                                           # artillery: hit any non-own non-king piece
            targets = None
            for i in range(N * N):
                pc = sq[i]
                if pc is not None and pc[0] == p and pc[1] == BISHOP and not self.cd.get(i):
                    if targets is None:
                        targets = [t for t in range(N * N) if sq[t] is not None and hs[sq[t][0]] and sq[t][1] != KING]
                    for t in targets:
                        ap((i, t, 5))
        return out

    def _heli(self, i, p, ap):
        hs = self.foes(p)
        sq, ok, N = self.sq, self.ok, self.N
        r, c = divmod(i, N)
        for dr, dc in KN_D:
            vr, vc = r + dr, c + dc
            if not (0 <= vr < N and 0 <= vc < N and ok[vr * N + vc]):
                continue
            v = vr * N + vc
            x = sq[v]
            if x is not None and (not hs[x[0]] or x[1] == KING):
                continue
            for er, ec in KN_D:
                wr, wc = vr + er, vc + ec
                if 0 <= wr < N and 0 <= wc < N and ok[wr * N + wc]:
                    w = wr * N + wc
                    y = sq[w]
                    if w == i:                         # out and back: only when the first landing captures
                        if x is not None:
                            ap((i, w, 1000 + v))
                    elif not (y is not None and (not hs[y[0]] or y[1] == KING)):
                        ap((i, w, 1000 + v))

    def blast_squares(self, t, p):
        sq, ok, N = self.sq, self.ok, self.N
        r, c = divmod(t, N)
        out = []
        for dr, dc in KG_D:
            nr, nc = r + dr, c + dc
            if 0 <= nr < N and 0 <= nc < N and ok[nr * N + nc]:
                x = sq[nr * N + nc]
                if x is not None and x[1] != KING and (JET_HITS_OWN or self.is_foe(p, x)):
                    out.append(nr * N + nc)
        return out

    def _castles(self, i, p, ap):
        sq, s = self.sq, self.step[p]
        if self.attacked(i, p):
            return
        rights = self.cr[p]
        if "K" in rights and sq[i + s] is None and sq[i + 2 * s] is None and sq[i + 3 * s] == (p, ROOK) \
                and not self.attacked(i + s, p) and not self.attacked(i + 2 * s, p):
            ap((i, i + 2 * s, 2))
        if "Q" in rights and sq[i - s] is None and sq[i - 2 * s] is None and sq[i - 3 * s] is None \
                and sq[i - 4 * s] == (p, ROOK) \
                and not self.attacked(i - s, p) and not self.attacked(i - 2 * s, p):
            ap((i, i - 2 * s, 3))

    def attacked(self, s, me):
        sq, ok, al, N = self.sq, self.ok, self.alive, self.N
        r, c = divmod(s, N)
        foe = [o != me and al[o] and not (self.teams and o % 2 == me % 2) for o in range(4)]
        for q in range(4):
            if not foe[q]:
                continue
            dr, dc = FDIRS[q]
            pr_, pc_ = (0, 1) if dr else (1, 0)
            for sg in (-1, 1):
                rr, cc = r - dr - sg * pr_, c - dc - sg * pc_
                if 0 <= rr < N and 0 <= cc < N:
                    x = sq[rr * N + cc]
                    if x is not None and x[0] == q and x[1] == PAWN:
                        return True
        for dirs, kind in ((KN_D, KNIGHT), (KG_D, KING)):
            for dr, dc in dirs:
                nr, nc = r + dr, c + dc
                if 0 <= nr < N and 0 <= nc < N:
                    x = sq[nr * N + nc]
                    if x is not None and x[1] == kind and foe[x[0]]:
                        return True
        for dirs, kind in ((ORTH, ROOK), (DIAG, BISHOP)):
            for dr, dc in dirs:
                nr, nc = r + dr, c + dc
                if self.army and kind == ROOK:          # tanks roll over everything except their own pieces and kings
                    owners, first = set(), True
                    while 0 <= nr < N and 0 <= nc < N and ok[nr * N + nc]:
                        x = sq[nr * N + nc]
                        if x is not None:
                            o = x[0]
                            if foe[o] and ((x[1] == ROOK and (o % 2 if self.teams else o) not in owners) or (x[1] == QUEEN and first)):
                                return True
                            if x[1] == KING:
                                break
                            if al[o]:
                                owners.add(o % 2 if self.teams else o)
                            first = False
                        nr += dr
                        nc += dc
                    continue
                while 0 <= nr < N and 0 <= nc < N and ok[nr * N + nc]:
                    x = sq[nr * N + nc]
                    if x is not None:
                        if foe[x[0]] and (x[1] == kind or x[1] == QUEEN):
                            return True
                        break
                    nr += dr
                    nc += dc
        return False

    def make(self, m, p):
        f, t, fl = m
        sq = self.sq
        pc, cap, old = sq[f], (sq[t] if t != f else None), self.cr
        extra = None
        old_cd = self.cd
        ticked = {}
        for s, n in old_cd.items():                    # the mover's artillery cooldowns tick down
            if sq[s] is not None and sq[s][0] == p:
                n -= 1
            if n > 0:
                ticked[s] = n
        if fl == 5:                                    # ranged shot: shooter stays put
            sq[t] = None
            touched = [t]
        else:
            sq[f] = None
            sq[t] = (p, PROMO4[fl]) if fl in PROMO4 else pc
            if fl == 2 or fl == 3:
                s = self.step[p]
                if fl == 2:
                    sq[f + s], sq[f + 3 * s] = sq[f + 3 * s], None
                else:
                    sq[f - s], sq[f - 4 * s] = sq[f - 4 * s], None
            elif fl == 9:                              # tank: crushes every piece it rolls over
                extra = [(n, sq[n]) for n in roll_path(f, t, self.N) if sq[n] is not None]
                for n, _ in extra:
                    sq[n] = None
            elif fl >= 1000:
                v = fl - 1000
                if sq[v] is not None:
                    extra = [(v, sq[v])]
                    sq[v] = None
            if self.army and pc[1] == QUEEN and cap is not None:          # jet blast
                bl = self.blast_squares(t, p)
                if bl:
                    extra = (extra or []) + [(n, sq[n]) for n in bl]
                    for n in bl:
                        sq[n] = None
            if pc[1] == KING:
                self.kings[p] = t
            touched = [f, t]
        if self.rook_home:
            if extra:
                touched = touched + [n for n, _ in extra]
            rm = set()
            if pc[1] == KING and f == self.king_home[p] and fl != 5:
                rm.update(((p, "K"), (p, "Q")))
            for sqi in touched:
                if sqi in self.rook_home:
                    rm.add(self.rook_home[sqi])
            if rm:
                new = list(old)
                for q, side in rm:
                    new[q] = new[q] - {side}
                self.cr = tuple(new)
        if old_cd or (fl == 5 and pc[1] == BISHOP):
            new = ticked
            new.pop(t, None)
            for n2, _ in (extra or ()):
                new.pop(n2, None)
            if fl == 5:
                if pc[1] == BISHOP:
                    new[f] = ARTILLERY_COOLDOWN
            elif f in new:
                new[t] = new.pop(f)
            self.cd = new
        return (f, t, pc, cap, old, fl, extra, old_cd)

    def unmake(self, u):
        f, t, pc, cap, old, fl, extra, old_cd = u
        self.cd = old_cd
        p = pc[0]
        sq = self.sq
        sq[t] = cap
        sq[f] = pc
        if fl == 2 or fl == 3:
            s = self.step[p]
            if fl == 2:
                sq[f + 3 * s], sq[f + s] = sq[f + s], None
            else:
                sq[f - 4 * s], sq[f - s] = sq[f - s], None
        if extra:
            for n, x in extra:
                sq[n] = x
        if pc[1] == KING:
            self.kings[p] = f
        self.cr = old

    def legal(self, p):
        res = []
        for m in self.pseudo(p):
            u = self.make(m, p)
            if not self.attacked(self.kings[p], p):
                res.append(m)
            self.unmake(u)
        return res

    def in_check(self, p):
        return self.attacked(self.kings[p], p)


def bot4_move(b, p, elo, legal):
    noise, rand_p = LEVELS4[elo]
    if random.random() < rand_p:
        return random.choice(legal)
    attacked_from = {}
    best, best_s = None, -1e9
    mid = (b.N - 1) / 2
    for m in legal:
        f, t, fl = m
        pc, cap = b.sq[f], b.sq[t]
        kind = pc[1]
        gain = POINTS[cap[1]] if (cap and b.alive[cap[0]]) else 0
        loss = 0.0
        if b.army:
            extra_sq = [fl - 1000] if fl >= 1000 else []
            if fl == 9:
                extra_sq = roll_path(f, t, b.N)
            if kind == QUEEN and cap and fl != 5:
                extra_sq += b.blast_squares(t, p)
            for n in extra_sq:
                x = b.sq[n]
                if x is None:
                    continue
                if not b.is_foe(p, x):
                    loss += SAFE_V[x[1]]
                elif b.alive[x[0]]:
                    gain += POINTS[x[1]]
        dest = f if fl == 5 else t
        if f not in attacked_from:
            attacked_from[f] = b.attacked(f, p)
        u = b.make(m, p)
        s = gain - loss + (8 if fl == 1 else 0) + (0.4 if fl in (2, 3) else 0)
        if b.attacked(dest, p):
            s -= SAFE_V[kind] * (0.9 if not gain else 0.6)
        if attacked_from[f]:
            s += SAFE_V[kind] * 0.5
        if elo >= 900:
            for q in range(4):
                if q != p and b.alive[q] and b.hostile[p][q] and b.attacked(b.kings[q], q):
                    s += 1.2
                    if elo >= 1100 and not b.legal(q):
                        s += 20
        b.unmake(u)
        r, c = divmod(t, b.N)
        if kind in (KNIGHT, BISHOP, PAWN) and fl != 5:
            s += (mid - abs(r - mid) + mid - abs(c - mid)) * 0.04
        if kind == QUEEN and gain == 0:
            s -= 0.3
        s += random.gauss(0, noise)
        if s > best_s:
            best, best_s = m, s
    return best


# ----------------------------------------------------------------------------
# Rendering helpers
# ----------------------------------------------------------------------------
W, H = 1000, 760
BOARD_PX = 720
LIGHT, DARK = (238, 216, 180), (172, 128, 92)
BG = (36, 34, 32)
PANEL = (50, 47, 44)
TEXT = (235, 232, 226)
MUTED = (160, 155, 148)
ACCENT = (110, 170, 90)


class Glyphs:
    def __init__(self):
        self.path = None
        for name in ("applesymbols", "arialunicodems", "dejavusans", "segoeuisymbol",
                     "notosanssymbols2", "symbola", "freeserif", "menlo", "arial"):
            path = pygame.font.match_font(name)
            if not path:
                continue
            try:
                f = pygame.font.Font(path, 40)
                if all(m is not None for m in f.metrics("".join(GLYPH.values()))):
                    self.path = path
                    break
            except Exception:
                pass
        self.cache = {}
        self.fonts = {}

    def get(self, kind, fill, outline, size, label=None):
        key = (kind, fill, outline, size, label)
        if len(self.cache) > 1500:
            self.cache.clear()
        s = self.cache.get(key)
        if s is not None:
            return s
        if self.path:
            fs = int(size * 0.92)
            font = self.fonts.setdefault(fs, pygame.font.Font(self.path, fs))
            base = font.render(GLYPH[kind], True, fill)
            edge = font.render(GLYPH[kind], True, outline)
            w, h = base.get_size()
            s = pygame.Surface((w + 4, h + 4), pygame.SRCALPHA)
            for dx in (0, 2, 4):
                for dy in (0, 2, 4):
                    if (dx, dy) != (2, 2):
                        s.blit(edge, (dx, dy))
            s.blit(base, (2, 2))
        else:
            s = pygame.Surface((size, size), pygame.SRCALPHA)
            pygame.draw.circle(s, outline, (size // 2, size // 2), int(size * 0.42))
            pygame.draw.circle(s, fill, (size // 2, size // 2), int(size * 0.36))
            font = self.fonts.setdefault(("f", size), pygame.font.Font(None, int(size * 0.6)))
            lum = fill[0] * 0.3 + fill[1] * 0.6 + fill[2] * 0.1
            t = font.render(LETTER[kind] or "P", True, (20, 20, 20) if lum > 120 else (240, 240, 240))
            s.blit(t, t.get_rect(center=(size // 2, size // 2)))
        if label:
            lf = self.fonts.setdefault(("lbl", size), pygame.font.Font(None, max(13, size // 4)))
            t, sh = lf.render(label, True, (255, 255, 255)), lf.render(label, True, (0, 0, 0))
            pos = ((s.get_width() - t.get_width()) // 2, int(s.get_height() * 0.76))
            for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                s.blit(sh, (pos[0] + dx, pos[1] + dy))
            s.blit(t, pos)
        self.cache[key] = s
        return s


FONTS = {}


def font(size):
    if size not in FONTS:
        FONTS[size] = pygame.font.Font(None, size)
    return FONTS[size]


def text(surf, s, size, pos, color=TEXT, center=False, right=False):
    img = font(size).render(s, True, color)
    rect = img.get_rect()
    if center:
        rect.center = pos
    elif right:
        rect.topright = pos
    else:
        rect.topleft = pos
    surf.blit(img, rect)
    return rect


def button(surf, rect, label, selected=False, enabled=True):
    mouse = pygame.mouse.get_pos()
    hover = rect.collidepoint(mouse) and enabled
    col = ACCENT if selected else (88, 84, 80) if hover else (68, 64, 60)
    if not enabled:
        col = (52, 50, 48)
    pygame.draw.rect(surf, col, rect, border_radius=8)
    text(surf, label, 26, rect.center, TEXT if enabled else MUTED, center=True)


def fmt_clock(t):
    t = max(0, t)
    return "%d:%02d" % (t // 60, t % 60) if t >= 10 else "%d:%04.1f" % (t // 60, t % 60)


# ----------------------------------------------------------------------------
# Game controllers
# ----------------------------------------------------------------------------
class AnimMixin:
    """0.5 second slide animations (4x faster when self.fast is set)."""
    anim = None
    fast = False

    def start_anim(self, items, ghosts, shots=(), blasts=(), span=1.0):
        self.anim = {"t0": time.time(), "dur": 0.12 if self.fast else 0.5, "items": items, "ghosts": ghosts,
                     "shots": shots, "blasts": blasts, "span": span, "cell": self.cell}

    def animating(self):
        a = self.anim
        if a and time.time() - a["t0"] >= a["dur"]:
            self.anim = None
        return self.anim is not None

    def hidden_squares(self):
        return {it[3] for it in self.anim["items"]} if self.anim else set()

    def draw_anim(self, s):
        a = self.anim
        if not a:
            return
        raw = min(1.0, (time.time() - a["t0"]) / a["dur"])
        span = a["span"]
        rm = min(1.0, raw / span)
        default_until = span if span < 1.0 else 0.85
        for g in a["ghosts"]:
            if raw < (g[2] if len(g) > 2 else default_until):
                s.blit(g[0], g[0].get_rect(center=g[1]))

        def lerp(p, q, e):
            return (p[0] + (q[0] - p[0]) * e, p[1] + (q[1] - p[1]) * e)

        def ease(u):
            return u * u * (3 - 2 * u)
        for it in a["items"]:
            img, c0, c1 = it[0], it[1], it[2]
            via = it[4] if len(it) > 4 else None
            if via is None:
                pos = lerp(c0, c1, ease(rm))
            elif rm < 0.5:
                pos = lerp(c0, via, ease(rm * 2))
            else:
                pos = lerp(via, c1, ease((rm - 0.5) * 2))
            s.blit(img, img.get_rect(center=pos))
        cell = a["cell"]
        for c0, c1 in a["shots"]:
            if raw < 0.7:
                pos = lerp(c0, c1, raw / 0.7)
                pygame.draw.line(s, (255, 190, 60), c0, pos, 3)
                pygame.draw.circle(s, (255, 240, 150), (int(pos[0]), int(pos[1])), max(4, cell // 7))
            else:
                rad = int(cell * 0.6 * (raw - 0.7) / 0.3)
                pygame.draw.circle(s, (255, 120, 40), (int(c1[0]), int(c1[1])), max(2, rad), 3)
        for c in a["blasts"]:
            if raw > span:
                rad = int(cell * 1.5 * (raw - span) / max(0.01, 1 - span))
                pygame.draw.circle(s, (255, 140, 40), c, max(2, rad), 4)
                pygame.draw.circle(s, (255, 225, 100), c, max(1, rad // 2), 3)


class ChoiceMixin:
    """Little popup used for promotions and for ambiguous army moves."""
    choice = None

    def open_choice(self, options):
        self.choice = options

    def choice_rects(self):
        w, h, gap = 300, 36, 6
        total = (h + gap) * len(self.choice) + 50
        x = 20 + (BOARD_PX - w) // 2
        y = 20 + (BOARD_PX - total) // 2
        return pygame.Rect(x, y, w, total), \
            [pygame.Rect(x + 12, y + 40 + i * (h + gap), w - 24, h) for i in range(len(self.choice))]

    def draw_choice(self, s):
        if not self.choice:
            return
        box, rects = self.choice_rects()
        pygame.draw.rect(s, (24, 22, 20), box, border_radius=12)
        pygame.draw.rect(s, ACCENT, box, 2, border_radius=12)
        text(s, "Choose (right-click cancels)", 24, (box.centerx, box.y + 20), TEXT, center=True)
        for (label, _), rect in zip(self.choice, rects):
            button(s, rect, label)

    def choice_click(self, pos):
        _, rects = self.choice_rects()
        for (label, mv), rect in zip(self.choice, rects):
            if rect.collidepoint(pos):
                self.choice = None
                self.play(mv)
                return
        self.cancel()


def draw_markers(s, moves, centers, cell, occupied, qsq=frozenset(), heli_min=100):
    """Draw legal-move hints: dot/ring = move, red cross-hair = fires, blue = double jump, orange = jet blast."""
    for m in sorted(moves, key=lambda mv: (mv[2] == 5, mv[2] >= heli_min)):
        t, fl = m[1], m[2]
        cx, cy = centers(t)
        if fl == 5:
            pygame.draw.circle(s, (220, 60, 50), (cx, cy), max(6, cell // 3), 3)
            d = max(8, cell // 2 - 4)
            pygame.draw.line(s, (220, 60, 50), (cx - d, cy), (cx + d, cy), 2)
            pygame.draw.line(s, (220, 60, 50), (cx, cy - d), (cx, cy + d), 2)
        elif fl == 9:                                      # tank rolls over pieces on the way
            pygame.draw.circle(s, (150, 90, 200), (cx, cy), max(5, cell // 2 - 3), 3)
            pygame.draw.rect(s, (150, 90, 200), (cx - cell // 8, cy - cell // 8, cell // 4, cell // 4))
        elif fl >= heli_min:
            pygame.draw.circle(s, (70, 130, 230), (cx, cy), max(5, cell // 2 - 3), 3)
            pygame.draw.circle(s, (70, 130, 230), (cx, cy), max(3, cell // 10))
        elif occupied(t):
            col = (240, 150, 40) if m[0] in qsq else (90, 160, 90)
            pygame.draw.circle(s, col, (cx, cy), max(6, cell // 2 - 2), 4)
        else:
            pygame.draw.circle(s, (90, 160, 90), (cx, cy), max(3, cell // 8))


def draw_cooldowns(s, cd, center, cell, hidden):
    """Small red badge with the turns left on every artillery that is reloading."""
    for sq_i, n in cd.items():
        if sq_i in hidden:
            continue
        cx, cy = center(sq_i)
        pos = (cx + cell // 2 - max(8, cell // 6), cy - cell // 2 + max(8, cell // 6))
        pygame.draw.circle(s, (200, 50, 45), pos, max(8, cell // 6))
        text(s, str(n), max(16, cell // 3), pos, (255, 255, 255), center=True)


def draw_legend(s, x, y):
    text(s, "Units", 22, (x, y), MUTED)
    y += 20
    for k in (PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING):
        n, a, blurb = ARMY_UNITS[k]
        text(s, "%s %s" % (a, blurb or n), 19, (x, y))
        y += 18
    return y + 8


class PlanMixin:
    """Planning marks: right-click a square to highlight it, right-drag between squares to draw an arrow.
    Any left click clears them.  They are only on your screen."""
    ARROW_COL = (60, 170, 70, 175)
    MARK_COL = (230, 80, 60, 130)
    arrows = frozenset()
    marks = frozenset()
    rdrag = None

    def plan_down(self, pos):
        self.rdrag = self.pos_to_sq(pos)

    def plan_up(self, pos):
        a, b = self.rdrag, self.pos_to_sq(pos)
        self.rdrag = None
        if a is None or b is None:
            return
        if a == b:
            self.marks = self.marks ^ {a}
        else:
            self.arrows = self.arrows ^ {(a, b)}

    def plan_clear(self):
        self.arrows, self.marks, self.rdrag = frozenset(), frozenset(), None

    def draw_marks(self, s):
        if not self.marks:
            return
        tint = pygame.Surface((self.cell, self.cell), pygame.SRCALPHA)
        tint.fill(self.MARK_COL)
        for i in self.marks:
            s.blit(tint, self.sq_to_xy(i))

    def draw_arrows(self, s):
        arrows = set(self.arrows)
        if self.rdrag is not None:                       # live preview while dragging
            cur = self.pos_to_sq(pygame.mouse.get_pos())
            if cur is not None and cur != self.rdrag:
                arrows.add((self.rdrag, cur))
        if not arrows:
            return
        layer = pygame.Surface((W, H), pygame.SRCALPHA)
        width = max(4, int(self.cell * 0.2))
        head = max(10, int(self.cell * 0.45))
        for a, b in arrows:
            (x1, y1), (x2, y2) = self.center(a), self.center(b)
            dx, dy = x2 - x1, y2 - y1
            d = max(1.0, (dx * dx + dy * dy) ** 0.5)
            ux, uy = dx / d, dy / d
            bx, by = x2 - ux * head, y2 - uy * head          # where the arrow head starts
            sx, sy = x1 + ux * self.cell * 0.25, y1 + uy * self.cell * 0.25
            px, py = -uy, ux
            hw, hh = width / 2, head * 0.55
            pygame.draw.polygon(layer, self.ARROW_COL, [
                (sx + px * hw, sy + py * hw), (bx + px * hw, by + py * hw), (bx + px * hh, by + py * hh),
                (x2, y2), (bx - px * hh, by - py * hh), (bx - px * hw, by - py * hw), (sx - px * hw, sy - py * hw)])
        s.blit(layer, (0, 0))


class Game2P(AnimMixin, ChoiceMixin, PlanMixin):
    def __init__(self, glyphs, variant, elo, side):
        self.g = glyphs
        self.variant, self.elo = variant, elo
        self.army = variant in ("army", "fullarmy")
        self.board = Board({"military": "military", "army": "army", "fullarmy": "fullarmy"}.get(variant, "normal"))
        self.human = side
        self.flip = side == -1
        self.sel, self.sel_moves = None, []
        self.last = None
        self.legal = self.board.legal()
        self.result = None
        self.log = []
        self.thinking, self.bot_done, self.bot_move, self.bot_start = False, False, None, 0
        self.blitz = variant == "blitz"
        self.clock = {1: 180.0, -1: 180.0}
        self.inc = 2
        self.tick = time.time()
        self.cell = min(BOARD_PX // self.board.cols, BOARD_PX // self.board.rows)
        self.ox = 20 + (BOARD_PX - self.cell * self.board.cols) // 2
        self.oy = 20 + (BOARD_PX - self.cell * self.board.rows) // 2
        self.dead = False
        self.title = {"normal": "Normal Chess", "blitz": "Blitz 3+2", "military": "Army Chess",
                      "army": "Military Chess", "fullarmy": "Full Military"}[variant]

    # geometry
    def sq_to_xy(self, i):
        r, c = divmod(i, self.board.cols)
        if self.flip:
            return self.ox + (self.board.cols - 1 - c) * self.cell, self.oy + r * self.cell
        return self.ox + c * self.cell, self.oy + (self.board.rows - 1 - r) * self.cell

    def center(self, i):
        x, y = self.sq_to_xy(i)
        return x + self.cell // 2, y + self.cell // 2

    def pos_to_sq(self, pos):
        x, y = pos[0] - self.ox, pos[1] - self.oy
        if not (0 <= x < self.cell * self.board.cols and 0 <= y < self.cell * self.board.rows):
            return None
        c, rr = x // self.cell, y // self.cell
        if self.flip:
            return rr * self.board.cols + (self.board.cols - 1 - c)
        return (self.board.rows - 1 - rr) * self.board.cols + c

    def name(self, i):
        r, c = divmod(i, self.board.cols)
        return "%s%d" % (chr(97 + c), r + 1)

    def kname(self, kind):
        return ARMY_UNITS[kind][0] if self.army else PIECE_NAME[kind].capitalize()

    def piece_img(self, p):
        white = p > 0
        return self.g.get(abs(p), (246, 246, 240) if white else (28, 28, 30),
                          (40, 40, 40) if white else (210, 210, 205), self.cell,
                          ARMY_UNITS[abs(p)][1] if self.army else None)

    # notation
    def move_text(self, m):
        f, t, fl = m
        b = self.board
        if fl == 2:
            return "O-O"
        if fl == 3:
            return "O-O-O"
        L = LETTER[abs(b.sq[f])]
        if fl == 5:
            return L + self.name(f) + "*" + self.name(t)
        if fl >= 100:
            return L + self.name(f) + "-" + self.name(fl - 100) + "-" + self.name(t)
        cap = b.sq[t] != 0 or fl == 1
        s = L + self.name(f) + ("x" if cap else "-") + self.name(t)
        if self.army and abs(b.sq[f]) == QUEEN and b.sq[t]:
            s += "*"
        if fl in PROMO_KIND:
            s += "=" + LETTER[PROMO_KIND[fl]]
        return s

    # choices
    def build_options(self, cands):
        moves = []
        for m in cands:
            if m[2] == 4:
                moves += [(m[0], m[1], fl) for fl in (4, 6, 7, 8)]
            else:
                moves.append(m)
        plain = {m[1] for m in moves if m[2] == 0}
        seen, out = set(), []
        for m in moves:
            if m[2] >= 100 and self.board.sq[m[2] - 100] == 0:
                if m[1] in plain or m[1] in seen:
                    continue
                seen.add(m[1])
            out.append((self.option_label(m, moves), m))
        return out

    def option_label(self, m, group):
        f, t, fl = m
        if fl in PROMO_KIND:
            return "Promote to " + self.kname(PROMO_KIND[fl])
        if fl == 5:
            return "Fire (stay in place)"
        if fl >= 100:
            return ("Jump out and back, hitting " if t == f else "Double jump via ") + self.name(fl - 100)
        if any(g[2] == 5 for g in group):
            return "Move and capture"
        if any(g[2] >= 100 for g in group):
            return "Single jump"
        return "Move"

    def cancel(self):
        self.sel, self.sel_moves, self.choice = None, [], None

    # play
    def play(self, m):
        b = self.board
        mover = b.turn
        f, t, fl = m
        p = b.sq[f]
        items, ghosts, shots, blasts, span = [], [], [], [], 1.0
        if fl != 5:
            via = self.center(fl - 100) if fl >= 100 else None
            items.append((self.piece_img(p), self.center(f), self.center(t), t, via))
        if fl == 2:
            items.append((self.piece_img(b.sq[f + 3]), self.center(f + 3), self.center(f + 1), f + 1))
        elif fl == 3:
            items.append((self.piece_img(b.sq[f - 4]), self.center(f - 4), self.center(f - 1), f - 1))
        txt = self.move_text(m)
        u = b.make(m)
        cap, extra = u[2], u[6] or []
        b.history.append(b.key())
        if fl == 5:
            shots.append((self.center(f), self.center(t)))
            ghosts.append((self.piece_img(cap), self.center(t), 0.7))
        elif fl == 1:
            ghosts.append((self.piece_img(cap), self.center(t - mover * b.cols)))
        elif cap:
            ghosts.append((self.piece_img(cap), self.center(t)))
        is_heli = fl >= 100
        if self.army and abs(p) == QUEEN and cap and fl != 5:
            blasts.append(self.center(t))
            span = 0.7
        for s2, v in extra:
            until = 0.5 if is_heli else 0.7
            if fl == 9:                                   # crushed as the tank passes over it
                span_t = max(abs(t // b.cols - f // b.cols), abs(t % b.cols - f % b.cols), 1)
                until = 0.9 * max(abs(s2 // b.cols - f // b.cols), abs(s2 % b.cols - f % b.cols)) / span_t
            ghosts.append((self.piece_img(v), self.center(s2), until))
        self.start_anim(items, ghosts, shots, blasts, span)
        if self.blitz:
            self.clock[mover] += self.inc
        self.last = (f, t)
        self.legal = b.legal()
        self.cancel()
        if b.in_check() and self.legal:
            txt += "+"
        elif not self.legal and b.in_check():
            txt += "#"
        self.log.append(txt)
        self.check_end()

    def check_end(self):
        b = self.board
        if not self.legal:
            if b.in_check():
                self.result = "Checkmate - %s wins!" % ("White" if b.turn == -1 else "Black")
            else:
                self.result = "Stalemate - draw"
        elif b.halfmove >= 100:
            self.result = "Draw - 50 move rule"
        elif b.history.count(b.key()) >= 3:
            self.result = "Draw - threefold repetition"
        elif not b.military and b.insufficient():
            self.result = "Draw - insufficient material"

    def resign(self):
        if not self.result:
            self.result = "You resigned"

    def click(self, pos):
        if self.result or self.board.turn != self.human or self.thinking or self.animating():
            return
        if self.choice:
            self.choice_click(pos)
            return
        i = self.pos_to_sq(pos)
        if i is None:
            return
        if self.sel is not None:
            cands = [m for m in self.sel_moves if m[1] == i]
            if cands:
                opts = self.build_options(cands)
                if len(opts) == 1 and opts[0][1][0] != opts[0][1][1]:   # out-and-back always asks first
                    self.play(opts[0][1])
                else:
                    self.open_choice(opts)
                return
        if self.board.sq[i] * self.human > 0:
            self.sel = i
            self.sel_moves = [m for m in self.legal if m[0] == i]
        else:
            self.cancel()

    def time_limit(self):
        tl = LEVELS[self.elo][3]
        if self.blitz:
            c = self.clock[-self.human]
            tl = min(tl, max(0.15, c / 30 + self.inc * 0.5))
        return tl

    def update(self):
        now = time.time()
        dt, self.tick = now - self.tick, now
        busy = self.animating()
        if self.result:
            return
        turn = self.board.turn
        if self.blitz and not busy:                         # clocks pause while a piece is sliding
            self.clock[turn] -= dt
            if self.clock[turn] <= 0:
                self.clock[turn] = 0
                loser = "White" if turn == 1 else "Black"
                self.result = "%s ran out of time - %s wins!" % (loser, "Black" if turn == 1 else "White")
                return
        if busy:
            return
        if turn != self.human and not self.thinking:
            self.thinking, self.bot_done, self.bot_move, self.bot_start = True, False, None, now
            b, elo, tl = self.board.copy(), self.elo, self.time_limit()

            def work():
                try:
                    mv = choose_move(b, elo, tl)
                except Exception as exc:  # never let the bot thread die silently
                    print("bot error:", exc)
                    mv = None
                self.bot_move, self.bot_done = mv, True
            threading.Thread(target=work, daemon=True).start()
        elif self.thinking and self.bot_done and now - self.bot_start > 0.3:
            self.thinking = False
            mv = self.bot_move
            if mv not in self.legal:
                mv = random.choice(self.legal)
            self.play(mv)

    # draw
    def draw(self, s):
        b = self.board
        cell = self.cell
        self.animating()
        hidden = self.hidden_squares()
        king_sq = b.kings[b.turn] if (b.in_check() and not self.result) else -1
        for i in range(len(b.sq)):
            x, y = self.sq_to_xy(i)
            r, c = divmod(i, b.cols)
            pygame.draw.rect(s, LIGHT if (r + c) % 2 else DARK, (x, y, cell, cell))
            if self.last and i in self.last:
                pygame.draw.rect(s, (205, 210, 100), (x, y, cell, cell), 0)
                pygame.draw.rect(s, LIGHT if (r + c) % 2 else DARK, (x + 3, y + 3, cell - 6, cell - 6))
            if i == king_sq:
                pygame.draw.rect(s, (220, 60, 50), (x, y, cell, cell), 4)
            if i == self.sel:
                pygame.draw.rect(s, (250, 230, 90), (x, y, cell, cell), 4)
        self.draw_marks(s)
        for i, p in enumerate(b.sq):
            if p and i not in hidden:
                img = self.piece_img(p)
                s.blit(img, img.get_rect(center=self.center(i)))
        draw_cooldowns(s, b.cd, self.center, cell, hidden)
        qsq = {self.sel} if (self.army and self.sel is not None and abs(b.sq[self.sel]) == QUEEN) else frozenset()
        draw_markers(s, self.sel_moves, self.center, cell, lambda t: b.sq[t] != 0, qsq, 100)
        self.draw_arrows(s)
        for c in range(b.cols):
            col = c if not self.flip else b.cols - 1 - c
            text(s, chr(97 + col), 18, (self.ox + c * cell + cell - 12, self.oy + b.rows * cell - 16), (60, 50, 40))
        for r in range(b.rows):
            row = (b.rows - 1 - r) if not self.flip else r
            text(s, str(row + 1), 18, (self.ox + 3, self.oy + r * cell + 3), (60, 50, 40))
        self.draw_anim(s)
        self.draw_panel(s)
        self.draw_choice(s)
        if self.result and not self.anim:
            overlay(s, self.result, self.HINT)

    # panel text (overridden by the LAN game)
    HINT = "Restart for a rematch, or go back to the menu"
    opp_label = "Bot"
    me_label = "You"

    def side_text(self):
        return "You play " + ("White" if self.human == 1 else "Black")

    def subtitle(self):
        return "Bot - Elo %d" % self.elo

    def status_text(self):
        if self.result:
            return "Game over"
        if self.board.turn != self.human:
            return "Bot thinking..."
        return "Check! Your move" if self.board.in_check() else "Your move"

    def draw_panel(self, s):
        px = 760
        pygame.draw.rect(s, PANEL, (px - 10, 0, W - px + 10, H))
        text(s, self.title, 34, (px, 22))
        text(s, self.subtitle(), 26, (px, 62), MUTED)
        opp, me = -self.human, self.human
        if self.blitz:
            text(s, self.opp_label + " " + fmt_clock(self.clock[opp]), 34, (px, 100), TEXT if self.board.turn == opp else MUTED)
            text(s, self.me_label + " " + fmt_clock(self.clock[me]), 34, (px, 135), TEXT if self.board.turn == me else MUTED)
        text(s, self.status_text(), 28, (px, 185), ACCENT)
        text(s, self.side_text(), 22, (px, 215), MUTED)
        y = 245
        if self.army:
            y = draw_legend(s, px, y)
        self.draw_log(s, px, y)
        for label, rect in self.buttons():
            button(s, rect, label)

    def draw_log(self, s, px, y):
        self.draw_moves(s, px, y, 640)

    def draw_moves(self, s, px, y, bottom):
        rows = [self.log[i:i + 2] for i in range(0, len(self.log), 2)]
        n_show = max(1, (bottom - y) // 22)
        for n, pair in enumerate(rows[-n_show:], max(1, len(rows) - n_show + 1)):
            text(s, "%d." % n, 22, (px, y), MUTED)
            text(s, pair[0], 22, (px + 38, y))
            if len(pair) > 1:
                text(s, pair[1], 22, (px + 120, y))
            y += 22

    def buttons(self):
        return [("Menu", pygame.Rect(760, 650, 100, 40)), ("Restart", pygame.Rect(870, 650, 100, 40)),
                ("Flip board", pygame.Rect(760, 700, 100, 40)), ("Resign", pygame.Rect(870, 700, 100, 40))]

    def press(self, label):
        if label == "Flip board":
            self.flip = not self.flip
        elif label == "Resign":
            self.resign()
        return label


class Game4P(AnimMixin, ChoiceMixin, PlanMixin):
    rot = 0
    HINT = "Restart for a rematch, or go back to the menu"          # quarter turns the view is rotated so the local player's pieces sit at the bottom

    def __init__(self, glyphs, elo, layout="standard", army=False, teams=False, human=0):
        self.g = glyphs
        self.elo = elo
        self.army = army
        self.teams = teams
        self.b = Board4(layout, army, teams)
        self.N = self.b.N
        self.cell = BOARD_PX // self.N
        self.ox = 20 + (BOARD_PX - self.cell * self.N) // 2
        self.oy = 20 + (BOARD_PX - self.cell * self.N) // 2
        self.human = self.rot = human       # the board is turned so your pieces are at the bottom
        self.sel, self.sel_moves = None, []
        self.last = None
        self.result = None
        self.log = []
        self.legal = self.b.legal(0)
        self.pause_until = 0.0
        self.fade = {}
        self.banner = None
        self.fast = False
        self.dead = False
        self.title = "4 Player" + ((" Full Military" if army else " Army") if layout == "military" else
                                   (" Military" if army else "")) \
            + (" 2v2" if teams else "")

    def name(self, i):
        r, c = divmod(i, self.N)
        return "%s%d" % (chr(97 + c), r + 1)

    def kname(self, kind):
        return ARMY_UNITS[kind][0] if self.army else PIECE_NAME[kind].capitalize()

    def sq_to_xy(self, i):
        r, c = divmod(i, self.N)
        for _ in range(self.rot):                    # undo the board's per-seat clockwise rotation
            r, c = c, self.N - 1 - r
        return self.ox + c * self.cell, self.oy + (self.N - 1 - r) * self.cell

    def center(self, i):
        x, y = self.sq_to_xy(i)
        return x + self.cell // 2, y + self.cell // 2

    def pos_to_sq(self, pos):
        x, y = pos[0] - self.ox, pos[1] - self.oy
        if not (0 <= x < self.N * self.cell and 0 <= y < self.N * self.cell):
            return None
        r, c = self.N - 1 - y // self.cell, x // self.cell
        for _ in range(self.rot):
            r, c = self.N - 1 - c, r
        i = r * self.N + c
        return i if self.b.ok[i] else None

    def piece_color(self, p):
        if self.b.alive[p]:
            return PLAYER_COLORS[p]
        t0 = self.fade.get(p)
        if t0 is None:
            return DEAD_COLOR
        k = min(8, int((time.time() - t0) / 0.8 * 8)) / 8.0
        a, d = PLAYER_COLORS[p], DEAD_COLOR
        return tuple(int(a[j] + (d[j] - a[j]) * k) for j in range(3))

    def piece_img(self, pc):
        return self.g.get(pc[1], self.piece_color(pc[0]), (25, 25, 25), self.cell,
                          ARMY_UNITS[pc[1]][1] if self.army else None)

    # choices
    def build_options(self, cands):
        moves = []
        for m in cands:
            if m[2] == 1:
                moves += [(m[0], m[1], fl) for fl in (1, 4, 6, 7)]
            else:
                moves.append(m)
        plain = {m[1] for m in moves if m[2] == 0}
        seen, out = set(), []
        for m in moves:
            if m[2] >= 1000 and self.b.sq[m[2] - 1000] is None:
                if m[1] in plain or m[1] in seen:
                    continue
                seen.add(m[1])
            out.append((self.option_label(m, moves), m))
        return out

    def option_label(self, m, group):
        f, t, fl = m
        if fl in PROMO4:
            return "Promote to " + self.kname(PROMO4[fl])
        if fl == 5:
            return "Fire (stay in place)"
        if fl >= 1000:
            return ("Jump out and back, hitting " if t == f else "Double jump via ") + self.name(fl - 1000)
        if any(g[2] == 5 for g in group):
            return "Move and capture"
        if any(g[2] >= 1000 for g in group):
            return "Single jump"
        return "Move"

    def cancel(self):
        self.sel, self.sel_moves, self.choice = None, [], None

    def play(self, m):
        b = self.b
        p = b.turn
        f, t, fl = m
        pc = b.sq[f]
        items, ghosts, shots, blasts, span = [], [], [], [], 1.0
        if fl != 5:
            via = self.center(fl - 1000) if fl >= 1000 else None
            items.append((self.piece_img(pc), self.center(f), self.center(t), t, via))
        if fl == 2 or fl == 3:
            s = b.step[p]
            rf, rt = (f + 3 * s, f + s) if fl == 2 else (f - 4 * s, f - s)
            items.append((self.piece_img(b.sq[rf]), self.center(rf), self.center(rt), rt))
        cap0 = b.sq[t]
        if fl == 2:
            txt = "O-O"
        elif fl == 3:
            txt = "O-O-O"
        elif fl == 5:
            txt = "%s*%s" % (self.name(f), self.name(t))
        elif fl >= 1000:
            txt = "%s-%s-%s" % (self.name(f), self.name(fl - 1000), self.name(t))
        else:
            txt = "%s%s%s" % (self.name(f), "x" if cap0 else "-", self.name(t))
        self.log.append("%s: %s" % (PLAYER_NAMES[p][0], txt))
        u = b.make(m, p)
        cap, extra = u[3], u[6] or []
        got = [cap] + [x for _, x in extra]
        if any(x is not None and b.alive[x[0]] for x in got):
            b.since_cap = 0
        else:
            b.since_cap += 1
        b.score[p] += sum(POINTS[x[1]] for x in got if x is not None and b.alive[x[0]])
        if fl == 5:
            shots.append((self.center(f), self.center(t)))
            ghosts.append((self.piece_img(cap), self.center(t), 0.7))
        elif cap:
            ghosts.append((self.piece_img(cap), self.center(t)))
        if self.army and pc[1] == QUEEN and cap and fl != 5:
            blasts.append(self.center(t))
            span = 0.7
        for s2, v in extra:
            until = 0.5 if fl >= 1000 else 0.7
            if fl == 9:
                span_t = max(abs(t // self.N - f // self.N), abs(t % self.N - f % self.N), 1)
                until = 0.9 * max(abs(s2 // self.N - f // self.N), abs(s2 % self.N - f % self.N)) / span_t
            ghosts.append((self.piece_img(v), self.center(s2), until))
        self.start_anim(items, ghosts, shots, blasts, span)
        self.last = (f, t)
        self.cancel()
        self.pause_until = time.time() + (0.03 if self.fast else 0.15)
        self.advance(p)

    def advance(self, mover):
        b = self.b
        cur = mover
        while True:
            if b.over() or b.since_cap >= NOCAP_LIMIT:
                self.finish()
                return
            cur = (cur + 1) % 4
            if not b.alive[cur]:
                continue
            moves = b.legal(cur)
            if moves:
                b.turn, self.legal = cur, moves
                return
            b.alive[cur] = False
            if b.in_check(cur):
                b.score[mover] += 20
                note = "%s checkmated %s! (+20)" % (PLAYER_NAMES[mover], PLAYER_NAMES[cur])
            else:
                b.score[cur] += 20
                note = "%s is stalemated (+20)" % PLAYER_NAMES[cur]
            now = time.time()
            self.fade[cur] = now
            self.log.append(note)
            self.banner = (note, now + (0.6 if self.fast else 2.2))
            self.pause_until = max(self.pause_until, now + (0.2 if self.fast else 1.3))

    def team_score(self, t):
        return self.b.score[t] + self.b.score[t + 2]

    def finish(self):
        b = self.b
        if self.teams:
            a, c = self.team_score(0), self.team_score(1)
            out0 = not (b.alive[0] or b.alive[2])
            out1 = not (b.alive[1] or b.alive[3])
            if out1 and not out0:
                a_wins = True
            elif out0 and not out1:
                a_wins = False
            else:
                a_wins = None if a == c else a > c
            mine = self.human % 2
            self.result_neutral = "Draw - teams tied on %d" % a if a_wins is None else \
                ("Red & Yellow win! (%d - %d)" % (a, c) if a_wins else "Blue & Green win! (%d - %d)" % (c, a))
            if a_wins is None:
                self.result = "Draw - teams tied on %d" % a
            elif a_wins == (mine == 0):
                self.result = "Your team wins! (%d - %d)" % ((a, c) if mine == 0 else (c, a))
            else:
                self.result = "%s win! (%d - %d)" % (("Red & Yellow", a, c) if a_wins else ("Blue & Green", c, a))
            self.legal = []
            return
        top = max(b.score)
        winners = [PLAYER_NAMES[i] for i in range(4) if b.score[i] == top]
        self.result = ("%s wins with %d points!" % (winners[0], top)) if len(winners) == 1 \
            else "Draw - %s tied on %d" % (" & ".join(winners), top)
        self.result_neutral = self.result
        self.legal = []

    def resign(self):
        self.resign_seat(self.human)

    def resign_seat(self, p):
        if self.result or not self.b.alive[p]:
            return
        mover = self.b.turn
        self.b.alive[p] = False
        self.fade[p] = time.time()
        self.log.append("%s resigned" % PLAYER_NAMES[p])
        if mover == p:
            self.advance(p)

    def input_locked(self):
        return False

    def click(self, pos):
        b = self.b
        h = self.human
        if self.result or b.turn != h or not b.alive[h] or self.animating() or self.input_locked():
            return
        if self.choice:
            self.choice_click(pos)
            return
        i = self.pos_to_sq(pos)
        if i is None:
            return
        if self.sel is not None:
            cands = [m for m in self.sel_moves if m[1] == i]
            if cands:
                opts = self.build_options(cands)
                if len(opts) == 1 and opts[0][1][0] != opts[0][1][1]:   # out-and-back always asks first
                    self.play(opts[0][1])
                else:
                    self.open_choice(opts)
                return
        x = b.sq[i]
        if x is not None and x[0] == h:
            self.sel = i
            self.sel_moves = [m for m in self.legal if m[0] == i]
        else:
            self.cancel()

    def update(self):
        now = time.time()
        self.animating()
        if self.result:
            return
        if (self.b.turn == self.human and self.b.alive[self.human]) or self.anim or now < self.pause_until:
            return
        self.play(bot4_move(self.b, self.b.turn, self.elo, self.legal))

    def draw(self, s):
        b, cell, N = self.b, self.cell, self.N
        self.animating()
        hidden = self.hidden_squares()
        for r in range(N):
            for c in range(N):
                i = r * N + c
                if not b.ok[i]:
                    continue
                x, y = self.sq_to_xy(i)
                pygame.draw.rect(s, LIGHT if (r + c) % 2 else DARK, (x, y, cell, cell))
                if self.last and i in self.last:
                    pygame.draw.rect(s, (205, 210, 100), (x, y, cell, cell), 3)
                if i == self.sel:
                    pygame.draw.rect(s, (250, 230, 90), (x, y, cell, cell), 3)
        for p in range(4):
            if b.alive[p] and b.in_check(p):
                x, y = self.sq_to_xy(b.kings[p])
                pygame.draw.rect(s, (230, 40, 40), (x, y, cell, cell), 4)
        self.draw_marks(s)
        for i, pc in enumerate(b.sq):
            if pc and i not in hidden:
                img = self.piece_img(pc)
                s.blit(img, img.get_rect(center=self.center(i)))
        draw_cooldowns(s, b.cd, self.center, cell, hidden)
        qsq = {self.sel} if (self.army and self.sel is not None and b.sq[self.sel][1] == QUEEN) else frozenset()
        draw_markers(s, self.sel_moves, self.center, cell, lambda t: b.sq[t] is not None, qsq, 1000)
        self.draw_arrows(s)
        self.draw_anim(s)
        if self.banner and time.time() < self.banner[1]:
            box = pygame.Surface((520, 44), pygame.SRCALPHA)
            pygame.draw.rect(box, (20, 20, 20, 220), box.get_rect(), border_radius=10)
            s.blit(box, (20 + (BOARD_PX - 520) // 2, 20 + BOARD_PX // 2 - 22))
            text(s, self.banner[0], 30, (20 + BOARD_PX // 2, 20 + BOARD_PX // 2), TEXT, center=True)
        self.draw_panel(s)
        self.draw_choice(s)
        if self.result and not self.anim:
            overlay(s, self.result, self.HINT)

    def draw_panel(self, s):
        px = 760
        pygame.draw.rect(s, PANEL, (px - 10, 0, W - px + 10, H))
        text(s, self.title, 34 if len(self.title) < 16 else 28 if len(self.title) < 20 else 24, (px, 24))
        text(s, self.subtitle(), 20, (px, 58), MUTED)
        y = 92
        for p in range(4):
            col_dot = PLAYER_COLORS[p] if self.b.alive[p] else DEAD_COLOR
            pygame.draw.circle(s, col_dot, (px + 8, y + 10), 8)
            col = TEXT if self.b.turn == p and not self.result else MUTED
            text(s, self.seat_label(p), 28 if len(self.seat_label(p)) < 15 else 22, (px + 26, y), col)
            text(s, "%d" % self.b.score[p], 28, (W - 30, y), col, right=True)
            y += 30
        h = self.human
        status = "Game over" if self.result else ("Your move" if self.b.turn == h and self.b.alive[h]
                                                  else "%s to move" % PLAYER_NAMES[self.b.turn])
        text(s, status, 28, (px, y + 6), ACCENT)
        y += 40
        if self.teams:
            text(s, "Team score  %d - %d" % (self.team_score(0), self.team_score(1)), 22, (px, y - 4), TEXT)
            y += 22
        if self.army:
            y = draw_legend(s, px, y)
        self.draw_log(s, px, y)
        for label, rect in self.buttons():
            button(s, rect, label)

    def draw_log(self, s, px, y):
        self.draw_moves(s, px, y, 640)

    def draw_moves(self, s, px, y, bottom):
        n_show = max(1, (bottom - y) // 21)
        for line in self.log[-n_show:]:
            text(s, line, 21, (px, y), TEXT if "checkmated" in line else MUTED)
            y += 21

    def subtitle(self):
        return ("Teams 2v2" if self.teams else "Free-for-all") + " - Bots Elo ~%d" % self.elo

    def player_name(self, p):
        return "You" if p == self.human else PLAYER_NAMES[p]

    def seat_label(self, p):
        ally = self.teams and p == (self.human + 2) % 4
        return self.player_name(p) + (" (ally)" if ally else "") + ("" if self.b.alive[p] else " (out)")

    def buttons(self):
        return [("Menu", pygame.Rect(760, 650, 100, 40)), ("Restart", pygame.Rect(870, 650, 100, 40)),
                ("Resign", pygame.Rect(760, 700, 100, 40)),
                ("Speed: 4x" if self.fast else "Speed: 1x", pygame.Rect(870, 700, 100, 40))]

    def press(self, label):
        if label == "Resign":
            self.resign()
        elif label.startswith("Speed"):
            self.fast = not self.fast
        return label


def overlay(s, msg, hint="Restart for a rematch, or go back to the menu"):
    box = pygame.Surface((560, 110), pygame.SRCALPHA)
    pygame.draw.rect(box, (20, 20, 20, 225), box.get_rect(), border_radius=14)
    s.blit(box, (20 + (BOARD_PX - 560) // 2, 20 + BOARD_PX // 2 - 55))
    text(s, msg, 38, (20 + BOARD_PX // 2, 20 + BOARD_PX // 2 - 15), TEXT, center=True)
    text(s, hint, 22, (20 + BOARD_PX // 2, 20 + BOARD_PX // 2 + 25),
         MUTED, center=True)


# ----------------------------------------------------------------------------
# LAN play: challenge another player on the same network by IP address
# ----------------------------------------------------------------------------
# Protocol: one JSON object per line over TCP.  The challenger connects and sends
#   {"type": "challenge", "proto": 1, "name": ..., "variant": ..., "host_side": 1 | -1}
# the host answers {"type": "accept", "name": ...} or {"type": "decline", "reason": ...}.
# In game: {"type": "move", "m": [from, to, flag], "clock": secs}, "resign", "timeout", "rematch".
NET_PORT = 5555
NET_PROTO = 5
PING_EVERY, PEER_TIMEOUT = 4.0, 20.0     # keep-alive: a silent connection is dropped instead of hanging
LAN_VARIANTS = {"normal", "blitz", "military", "army", "fullarmy"}
LAN4_VARIANTS = {"4p", "4pmil", "4parmy", "4pfull"}


def move_ok(m, legal, promos, queen_flag):
    """Legal move lists only hold the queen promotion; the other promotion choices share its from/to squares."""
    if m in legal:
        return True
    f, t, fl = m
    return fl in promos and (f, t, queen_flag) in legal


def all_local_ips():
    ips = []
    try:
        for info in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            ip = info[4][0]
            if not ip.startswith("127.") and ip not in ips:
                ips.append(ip)
    except OSError:
        pass
    return ips


def connect_error(exc):
    """A short, useful explanation of why a challenge could not be delivered."""
    if isinstance(exc, ConnectionRefusedError):
        return "Not running", "the game isn't open there, or it couldn't open port %d" % NET_PORT
    if isinstance(exc, (socket.timeout, TimeoutError)):
        return "No answer", "wrong address, a different network, or a firewall blocking port %d" % NET_PORT
    if isinstance(exc, socket.gaierror):
        return "Bad address", "that address doesn't exist"
    return "Unreachable", str(getattr(exc, "strerror", None) or exc)


def local_ip():
    """Best guess at this machine's LAN address (no packets are actually sent)."""
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as u:
            u.connect(("10.255.255.255", 1))
            return u.getsockname()[0]
    except OSError:
        try:
            return socket.gethostbyname(socket.gethostname())
        except OSError:
            return "127.0.0.1"


def parse_address(s):
    """'192.168.1.20' or '192.168.1.20:6000' -> (host, port)."""
    s = s.strip()
    if s.count(":") == 1:
        host, port = s.split(":")
        return host.strip(), int(port)
    return s, NET_PORT


class Peer:
    """A connected opponent: newline-delimited JSON, read on a background thread into a queue."""

    def __init__(self, sock, addr):
        self.sock, self.addr = sock, addr[0]
        self.q = queue.Queue()
        self.alive = True
        self.lock = threading.Lock()
        self.last_rx = time.time()
        try:
            sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass
        threading.Thread(target=self._read, daemon=True).start()
        threading.Thread(target=self._keepalive, daemon=True).start()

    def _keepalive(self):
        while self.alive:
            time.sleep(PING_EVERY)
            if not self.alive:
                break
            if time.time() - self.last_rx > PEER_TIMEOUT:     # the other side vanished (sleep, Wi-Fi drop...)
                self.close()
                break
            self.send({"type": "ping"})

    def _read(self):
        try:
            for line in self.sock.makefile("r", encoding="utf-8"):
                self.last_rx = time.time()
                try:
                    msg = json.loads(line)
                except ValueError:
                    continue
                if isinstance(msg, dict) and msg.get("type") != "ping":
                    self.q.put(msg)
        except (OSError, ValueError):
            pass
        self.alive = False
        self.q.put({"type": "_closed"})

    def send(self, msg):
        data = (json.dumps(msg) + "\n").encode("utf-8")
        try:
            with self.lock:
                self.sock.sendall(data)
        except OSError:
            self.alive = False

    def get(self):
        try:
            return self.q.get_nowait()
        except queue.Empty:
            return None

    def close(self):
        self.alive = False
        try:
            self.sock.shutdown(socket.SHUT_RDWR)
        except OSError:
            pass
        try:
            self.sock.close()
        except OSError:
            pass


class Listener:
    """Accepts incoming challenge connections on NET_PORT."""

    def __init__(self, port=NET_PORT):
        self.port = port
        self.q = queue.Queue()
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        if hasattr(socket, "SO_EXCLUSIVEADDRUSE"):      # Windows: never share the port with a second copy
            self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_EXCLUSIVEADDRUSE, 1)
        else:
            self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.sock.bind(("", port))
        self.sock.listen(4)
        self.sock.settimeout(0.5)
        self.running = True
        threading.Thread(target=self._run, daemon=True).start()

    def _run(self):
        while self.running:
            try:
                c, a = self.sock.accept()
            except socket.timeout:
                continue
            except OSError:             # e.g. a connection reset before we accepted it: keep listening
                if not self.running:
                    break
                time.sleep(0.2)
                continue
            c.settimeout(None)
            self.q.put((c, a))

    def get(self):
        try:
            return self.q.get_nowait()
        except queue.Empty:
            return None

    def stop(self):
        self.running = False
        try:
            self.sock.close()
        except OSError:
            pass


CHAT_MAX = 150
ME_COLOR = (130, 200, 110)
OPP_COLOR = (120, 170, 235)


def clean_chat(t):
    return "".join(ch for ch in str(t) if ch.isprintable())[:CHAT_MAX].strip()


def wrap_px(s, size, width):
    """Greedy word wrap by rendered pixel width."""
    f, lines, cur = font(size), [], ""
    for word in s.split(" "):
        cand = word if not cur else cur + " " + word
        if f.size(cand)[0] <= width:
            cur = cand
            continue
        if cur:
            lines.append(cur)
        while f.size(word)[0] > width:               # a single word longer than the line
            n = len(word)
            while n > 1 and f.size(word[:n])[0] > width:
                n -= 1
            lines.append(word[:n])
            word = word[n:]
        cur = word
    lines.append(cur)
    return lines


class ChatMixin:
    """Chat for LAN games: a Moves / Chat tab pair in the side panel.  Enter opens the chat box and sends;
    Esc closes it.  In 2v2 games Tab (or the All / Team button) switches between public and team chat."""
    CHAT_SIZE = 20
    TAB_MOVES = pygame.Rect(760, 0, 112, 28)        # y is set when the panel is drawn
    TAB_CHAT = pygame.Rect(878, 0, 112, 28)
    CHAT_TOP_PAD = 36
    INPUT_Y = 604

    chat_readonly = False

    def chat_init(self):
        self.chat = []                # (who or None, text, color, team)
        self.chat_text = ""
        self.chat_focus = False
        self.tab = "moves"
        self.unread = 0
        self.team_chat = False
        self.tab_y = 245

    def inherit_chat(self, old):
        self.chat, self.tab, self.team_chat = old.chat, old.tab, old.team_chat
        self.chat_add(None, "- rematch started -", MUTED)

    def can_team_chat(self):
        return False

    def chat_add(self, who, msg, color, team=False):
        self.chat.append((who, msg, color, team))
        del self.chat[:-200]
        if self.tab != "chat":
            self.unread += 1

    def send_chat(self, msg, team):
        raise NotImplementedError

    # geometry
    def chat_rects(self):
        tm = self.TAB_MOVES.move(0, self.tab_y)
        tc = self.TAB_CHAT.move(0, self.tab_y)
        if self.can_team_chat():
            chan = pygame.Rect(760, self.INPUT_Y, 62, 36)
            box = pygame.Rect(826, self.INPUT_Y, 164, 36)
        else:
            chan, box = None, pygame.Rect(760, self.INPUT_Y, 230, 36)
        return tm, tc, chan, box

    def open_chat(self):
        self.tab, self.unread, self.chat_focus = "chat", 0, True

    # input
    def chat_key(self, e):
        """Returns True when the key was used by the chat."""
        if not self.chat_focus:
            if e.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
                self.open_chat()
                self.chat_focus = not self.chat_readonly
                return True
            return False
        if e.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
            msg = clean_chat(self.chat_text)
            if msg:
                self.send_chat(msg, self.team_chat and self.can_team_chat())
            self.chat_text = ""
        elif e.key == pygame.K_ESCAPE:
            self.chat_focus = False
        elif e.key == pygame.K_TAB:
            if self.can_team_chat():
                self.team_chat = not self.team_chat
        elif e.key == pygame.K_BACKSPACE:
            self.chat_text = self.chat_text[:-1]
        elif e.key == pygame.K_F11:
            return False
        elif e.unicode and e.unicode.isprintable() and len(self.chat_text) < CHAT_MAX:
            self.chat_text += e.unicode
        return True

    def chat_click(self, pos):
        """Returns True when the click was used by the chat."""
        tm, tc, chan, box = self.chat_rects()
        if tm.collidepoint(pos):
            self.tab, self.chat_focus = "moves", False
            return True
        if tc.collidepoint(pos):
            self.tab, self.unread = "chat", 0
            return True
        if self.tab == "chat" and chan and chan.collidepoint(pos):
            self.team_chat = not self.team_chat
            self.chat_focus = True
            return True
        if self.tab == "chat" and box.collidepoint(pos):
            self.chat_focus = not self.chat_readonly
            return True
        self.chat_focus = False
        return False

    # drawing (replaces the plain move list in the side panel)
    def draw_log(self, s, px, y):
        self.tab_y = y
        tm, tc, chan, box = self.chat_rects()
        button(s, tm, "Moves", self.tab == "moves")
        button(s, tc, "Chat (%d)" % self.unread if self.unread else "Chat", self.tab == "chat")
        y += self.CHAT_TOP_PAD
        if self.tab == "moves":
            self.draw_moves(s, px, y, 640)
            return
        size, lh, width = self.CHAT_SIZE, 19, 230
        lines = []
        for who, msg, color, team in self.chat:
            if who is None:
                lines += [(None, ln, color) for ln in wrap_px(msg, size, width)]
                continue
            prefix = ("[Team] " if team else "") + who + ": "
            wrapped = wrap_px(prefix + msg, size, width)
            lines.append((prefix, wrapped[0], color))
            lines += [(None, ln, TEXT) for ln in wrapped[1:]]
        n_show = max(1, (self.INPUT_Y - 6 - y) // lh)
        if not lines:
            text(s, "No messages yet.", size, (px, y), MUTED)
            text(s, "Press Enter to chat.", size, (px, y + lh), MUTED)
        for prefix, ln, color in lines[-n_show:]:
            if prefix and ln.startswith(prefix):
                r = text(s, prefix, size, (px, y), color)
                text(s, ln[len(prefix):], size, (r.right, y), TEXT)
            else:
                text(s, ln, size, (px, y), color)
            y += lh
        if chan:
            button(s, chan, "Team" if self.team_chat else "All", self.team_chat)
        pygame.draw.rect(s, (24, 22, 20), box, border_radius=6)
        pygame.draw.rect(s, ACCENT if self.chat_focus else (78, 74, 70), box, 2, border_radius=6)
        if self.chat_text or self.chat_focus:
            shown = self.chat_text
            while shown and font(size).size(shown + "|")[0] > box.w - 14:
                shown = shown[1:]
            caret = "|" if self.chat_focus and int(time.time() * 2) % 2 else ""
            text(s, shown + caret, size, (box.x + 7, box.y + 10))
        else:
            text(s, "Spectating - read only" if self.chat_readonly else
                 "Enter to chat" + (" (Tab: team)" if chan and box.w > 200 else ""), size,
                 (box.x + 7, box.y + 10), (110, 106, 100))


class SpecHostMixin:
    """Lets friends watch a LAN game through this player: they get a snapshot of every move so far, then each
    move as it is played, plus the public chat (never team chat).  Watchers can't affect the game."""
    MAX_SPECS = 8
    specs = ()

    def spec_init(self):
        self.specs = []               # [(Peer, name)]
        self.spec_result_sent = False

    def spec_info(self):
        raise NotImplementedError

    def spec_log(self):
        raise NotImplementedError

    def neutral_result(self):
        return self.result

    def add_spectator(self, peer, name, quiet=False):
        peer.send({"type": "spec_start", "info": self.spec_info(), "events": self.spec_log(),
                   "result": self.neutral_result() if self.result else None})
        self.specs.append((peer, name))
        if not quiet:
            self.chat_add(None, "%s is watching" % name, MUTED)

    def adopt_spectators(self, old):
        for peer, name in old.specs:
            if peer.alive:
                self.add_spectator(peer, name, quiet=True)
        old.specs = []

    def spec_send(self, msg):
        for peer, _ in self.specs:
            peer.send(msg)

    def spec_ev(self, ev):
        if not getattr(self, "replaying", False):
            self.spec_send({"type": "spec", "ev": ev})

    def chat_add(self, who, msg, color, team=False):
        super().chat_add(who, msg, color, team)
        if self.specs and not team:
            self.spec_send({"type": "spec_chat", "who": my_name() if who == "You" else who, "text": msg,
                            "color": list(color)})

    def spec_pump(self):
        for item in list(self.specs):
            peer, name = item
            while True:
                m = peer.get()
                if m is None:
                    break
                if m.get("type") == "_closed":
                    self.specs.remove(item)
                    self.chat_add(None, "%s stopped watching" % name, MUTED)
                    break
            if item in self.specs and not peer.alive:
                self.specs.remove(item)
        if self.result and not self.spec_result_sent:
            self.spec_result_sent = True
            self.spec_ev(["end", self.neutral_result()])

    def spec_close(self):
        for peer, _ in self.specs:
            peer.send({"type": "spec_end", "text": "The player you were watching through left the game"})
            peer.close()
        self.specs = []

    def watching_note(self):
        return "  - %d watching" % len(self.specs) if self.specs else ""


class NetGame2P(SpecHostMixin, ChatMixin, Game2P):
    """Two humans on different machines.  Both sides run the same deterministic board and swap moves."""
    HINT = "Rematch to play again with colors swapped, or go back"
    FLAG_GRACE = 5.0      # seconds we wait for the opponent's own client to report their time loss

    def __init__(self, glyphs, variant, side, peer, opp_name, back_to="lan"):
        super().__init__(glyphs, variant, ELOS[0], side)
        self.peer, self.opp_name, self.back_to = peer, opp_name, back_to
        self.chat_init()
        self.spec_init()
        self.spec_events = []
        self.opp_label = "Opp"
        self.title += " (LAN)"
        self.rematch_me = self.rematch_them = False
        self.next_game = None
        self.flag_since = None

    def subtitle(self):
        return "vs %s (%s)%s" % (self.opp_name[:12], self.peer.addr, self.watching_note())

    # spectators
    def spec_info(self):
        names = {self.human: my_name(), -self.human: self.opp_name}
        return {"kind": 2, "variant": self.variant, "white": names[1], "black": names[-1],
                "clock": {"1": round(self.clock[1], 2), "-1": round(self.clock[-1], 2)}}

    def spec_log(self):
        return self.spec_events

    def neutral_result(self):
        r, me = self.result, self.human
        if r == "You resigned":
            return "%s resigned - %s wins!" % (self.color(me), self.color(-me))
        if r == "Opponent resigned - you win!":
            return "%s resigned - %s wins!" % (self.color(-me), self.color(me))
        if r == "Opponent disconnected":
            return "%s disconnected" % self.color(-me)
        return r

    def status_text(self):
        if self.result:
            if self.rematch_me and not self.rematch_them:
                return "Rematch offered..."
            if self.rematch_them and not self.rematch_me:
                return "Opponent wants a rematch"
            return "Game over"
        if self.board.turn != self.human:
            return "Opponent's move"
        return "Check! Your move" if self.board.in_check() else "Your move"

    def color(self, side):
        return "White" if side == 1 else "Black"

    def play(self, m):
        local = self.board.turn == self.human
        super().play(m)
        ev = ["m", list(m), {"1": round(self.clock[1], 2), "-1": round(self.clock[-1], 2)}]
        self.spec_events.append(ev)
        self.spec_ev(ev)
        if local:
            self.peer.send({"type": "move", "m": list(m), "clock": round(self.clock[self.human], 2)})

    def resign(self):
        if not self.result:
            self.result = "You resigned"
            self.peer.send({"type": "resign"})

    def send_chat(self, msg, team):
        if not self.peer.alive:
            self.chat_add(None, "(not sent - opponent disconnected)", MUTED)
            return
        self.peer.send({"type": "chat", "text": msg})
        self.chat_add("You", msg, ME_COLOR)

    def close(self):
        """Leaving the game: resign if it is still running, then hang up."""
        self.resign()
        self.spec_pump()                      # lets watchers see the resignation
        self.spec_close()
        self.peer.close()

    def handle(self, msg):
        t = msg.get("type")
        if t == "move":
            try:
                mv = tuple(int(x) for x in msg["m"])
            except (KeyError, TypeError, ValueError):
                return
            if self.result or self.board.turn == self.human:
                return
            if not move_ok(mv, self.legal, PROMO_KIND, 4):
                self.result = "Out of sync - illegal move received"
                return
            self.play(mv)
            if isinstance(msg.get("clock"), (int, float)):
                self.clock[-self.human] = float(msg["clock"])
            self.flag_since = None
        elif t == "resign":
            if not self.result:
                self.result = "Opponent resigned - you win!"
        elif t == "timeout":
            if not self.result:
                self.clock[-self.human] = 0
                self.result = "%s ran out of time - %s wins!" % (self.color(-self.human), self.color(self.human))
        elif t == "rematch":
            self.rematch_them = True
        elif t == "chat":
            msg = clean_chat(msg.get("text", ""))
            if msg:
                self.chat_add(self.opp_name[:12], msg, OPP_COLOR)
        elif t == "_closed":
            if not self.result:
                self.result = "Opponent disconnected"
            self.rematch_them = False
            self.chat_add(None, "%s disconnected" % self.opp_name[:12], MUTED)

    def update(self):
        now = time.time()
        dt, self.tick = now - self.tick, now
        self.spec_pump()
        while True:
            if self.rematch_me and self.rematch_them and self.peer.alive:
                if self.next_game is None:
                    self.next_game = NetGame2P(self.g, self.variant, -self.human, self.peer, self.opp_name,
                                               self.back_to)
                    self.next_game.inherit_chat(self)
                break                            # later messages belong to the new game
            msg = self.peer.get()
            if msg is None:
                break
            self.handle(msg)
        if self.result or not self.blitz or self.animating():
            return
        turn = self.board.turn
        self.clock[turn] -= dt
        if turn == self.human and self.clock[turn] <= 0:          # we are the authority on our own clock
            self.clock[turn] = 0
            self.peer.send({"type": "timeout"})
            self.result = "%s ran out of time - %s wins!" % (self.color(turn), self.color(-turn))
        elif turn != self.human and self.clock[turn] <= 0:
            self.clock[turn] = 0
            self.flag_since = self.flag_since or now
            if now - self.flag_since > self.FLAG_GRACE:
                self.result = "%s ran out of time - %s wins!" % (self.color(turn), self.color(-turn))

    def buttons(self):
        if getattr(self, "tournament", False):
            return [("Menu", pygame.Rect(760, 650, 100, 40)), ("Flip board", pygame.Rect(760, 700, 100, 40)),
                    ("Resign", pygame.Rect(870, 700, 100, 40))]
        return [("Menu", pygame.Rect(760, 650, 100, 40)), ("Rematch", pygame.Rect(870, 650, 100, 40)),
                ("Flip board", pygame.Rect(760, 700, 100, 40)), ("Resign", pygame.Rect(870, 700, 100, 40))]

    def press(self, label):
        if label == "Rematch":
            if self.result and not self.rematch_me and self.peer.alive:
                self.rematch_me = True
                self.peer.send({"type": "rematch"})
            return label
        return super().press(label)


class NetGame4P(SpecHostMixin, ChatMixin, Game4P):
    """4 Player over the LAN.  The player who sent the challenges is the hub (any seat): it runs the bots,
    checks every move and relays it to everyone else, so all boards apply the same moves in the same order.
    Resignations take effect on the resigning player's own turn, so they can never race another move."""
    HINT = "The host can start a rematch, or go back"

    def __init__(self, glyphs, variant, teams, elo, seat, names, peers=None, host=None):
        super().__init__(glyphs, elo, "military" if variant in ("4pmil", "4pfull") else "standard",
                         variant in ("4parmy", "4pfull"), teams)
        self.variant = variant
        self.human = self.rot = seat
        self.names = list(names)              # player name per seat, None = bot
        self.peers = peers                    # hub: {seat: Peer}
        self.host = host                      # client: the hub's Peer
        self.is_hub = peers is not None
        self.back_to = "lan" if self.is_hub else "challenges"
        self.inq = deque()                    # client: messages from the hub, in order
        self.seat_q = {s: deque() for s in range(4)}   # hub: each remote seat's moves / resigns, in order
        self.pending_resign = set()
        self.resigning = False
        self.next_game = None
        self.title += " (LAN)"
        self.chat_init()
        self.events = []                      # every move / resignation in order (used to re-sync a player)
        self.spec_init()
        self.replaying = False
        self.resync_wait = False

    # chat: the hub relays everything; team messages only go to the sender's teammates
    def can_team_chat(self):
        return self.teams

    def send_chat(self, msg, team):
        if self.is_hub:
            self.relay_chat(self.human, msg, team)
        elif not self.host.alive:
            self.chat_add(None, "(not sent - the host left)", MUTED)
        else:
            self.host.send({"type": "chat", "text": msg, "team": team})
            self.chat_add("You", msg, PLAYER_COLORS[self.human], team)

    def relay_chat(self, p, msg, team):
        msg, team = clean_chat(msg), bool(team) and self.teams
        if not msg:
            return
        for seat, pr in list(self.peers.items()):
            if seat != p and (not team or seat % 2 == p % 2):
                pr.send({"type": "chat", "p": p, "text": msg, "team": team})
        if not team or self.human % 2 == p % 2:
            self.chat_add(self.player_name(p), msg, PLAYER_COLORS[p], team)

    # labels
    def subtitle(self):
        humans = sum(1 for n in self.names if n is not None)
        return "LAN - %d human%s%s%s" % (humans, "s" if humans != 1 else "",
                                         (", bots ~%d" % self.elo) if humans < 4 else "", self.watching_note())

    # spectators
    def spec_info(self):
        return {"kind": 4, "variant": self.variant, "teams": self.teams, "names": self.names, "elo": self.elo}

    def spec_log(self):
        return self.events

    def neutral_result(self):
        return getattr(self, "result_neutral", None) or self.result

    def player_name(self, p):
        if p == self.human:
            return "You"
        return self.names[p][:10] if self.names[p] else PLAYER_NAMES[p] + " bot"

    def input_locked(self):
        return self.resigning or bool(self.inq and not self.is_hub)

    # moves
    def broadcast(self, msg, skip=None):
        for s, pr in list(self.peers.items()):
            if s != skip:
                pr.send(msg)

    def play(self, m):
        mover = self.b.turn
        self.events.append(["m", mover, list(m)])
        super().play(m)
        if self.replaying:
            return
        self.spec_ev(["m", mover, list(m)])
        if self.is_hub:
            self.broadcast({"type": "move", "p": mover, "m": list(m)}, skip=mover)
        elif mover == self.human:
            self.host.send({"type": "move", "m": list(m)})

    def resign_seat(self, p):
        if not self.result and self.b.alive[p]:
            self.events.append(["r", p])
            super().resign_seat(p)
            self.spec_ev(["r", p])

    def legal_ok(self, mv):
        return move_ok(mv, self.legal, PROMO4, 1)

    def send_resync(self, s):
        if s in self.peers:
            self.peers[s].send({"type": "resync", "events": self.events, "names": self.names, "elo": self.elo})

    def rebuild(self, msg):
        """Client: replay the host's full history on a fresh board."""
        names, events = msg.get("names"), msg.get("events")
        if not (isinstance(names, list) and len(names) == 4 and isinstance(events, list)):
            return None
        g = NetGame4P(self.g, self.variant, self.teams, int(msg.get("elo", self.elo)), self.human, names,
                      host=self.host)
        g.replaying = True
        try:
            for ev in events:
                if ev[0] == "m":
                    mv = tuple(int(x) for x in ev[2])
                    if ev[1] != g.b.turn or not g.legal_ok(mv):
                        break
                    g.play(mv)
                elif ev[0] == "r":
                    g.resign_seat(int(ev[1]))
        except (IndexError, TypeError, ValueError):
            pass
        g.replaying = False
        g.anim, g.pause_until, g.banner = None, 0.0, None
        g.fade = {k: 0.0 for k in g.fade}
        g.resigning, g.fast = self.resigning, self.fast
        g.chat, g.tab, g.team_chat, g.unread = self.chat, self.tab, self.team_chat, self.unread
        g.chat_add(None, "Re-synced with the host", MUTED)
        return g

    def resign(self):
        if self.result or not self.b.alive[self.human] or self.resigning:
            return
        self.resigning = True
        self.log.append("You will resign on your turn" if self.b.turn != self.human else "Resigning...")
        if self.is_hub:
            self.pending_resign.add(self.human)
        else:
            self.host.send({"type": "resign"})

    def close(self):
        self.spec_close()
        if self.is_hub:
            for pr in self.peers.values():
                pr.close()
        else:
            self.resign()
            self.host.close()

    def update(self):
        self.animating()
        self.spec_pump()
        if self.is_hub:
            self.update_hub()
        else:
            self.update_client()

    def update_hub(self):
        now = time.time()
        for s, pr in list(self.peers.items()):
            while True:
                msg = pr.get()
                if msg is None:
                    break
                t = msg.get("type")
                if t in ("move", "resign"):
                    self.seat_q[s].append(msg)
                elif t == "chat":
                    self.relay_chat(s, msg.get("text", ""), msg.get("team"))
                elif t == "resync_req":
                    self.send_resync(s)
                elif t == "_closed":
                    del self.peers[s]
                    if self.names[s] is not None:
                        self.log.append("%s left - a bot takes over" % self.names[s][:12])
                        self.chat_add(None, "%s left the game" % self.names[s][:12], MUTED)
                    self.names[s] = None
                    self.broadcast({"type": "left", "p": s})
                    break
        if self.result or self.anim or now < self.pause_until:
            return
        b = self.b
        p = b.turn
        q = self.seat_q[p]
        while q:                                              # that seat's messages, in the order sent
            msg = q.popleft()
            if msg["type"] == "resign":
                self.pending_resign.add(p)
                break
            try:
                mv = tuple(int(x) for x in msg["m"])
            except (KeyError, TypeError, ValueError):
                continue
            if self.legal_ok(mv):
                self.play(mv)
                return
            q.clear()                                         # their board disagrees with ours: re-sync it
            self.send_resync(p)
            break
        if p in self.pending_resign:
            self.pending_resign.discard(p)
            self.resign_seat(p)
            self.broadcast({"type": "resign", "p": p})
            return
        if p == self.human or p in self.peers:
            return                                            # waiting for a human
        self.play(bot4_move(b, p, self.elo, self.legal))

    def update_client(self):
        now = time.time()
        while True:
            msg = self.host.get()
            if msg is None:
                break
            t = msg.get("type")
            if t == "_closed":
                if not self.result:
                    self.result = "The host left - game over"
                if self.host.alive is False and not getattr(self, "host_gone", False):
                    self.host_gone = True
                    self.chat_add(None, "The host left", MUTED)
            elif t == "chat":
                p, text_ = msg.get("p"), clean_chat(msg.get("text", ""))
                if p in (0, 1, 2, 3) and text_:
                    self.chat_add(self.player_name(p), text_, PLAYER_COLORS[p], bool(msg.get("team")) and self.teams)
            elif t == "left":
                p = msg.get("p")
                if p in (0, 1, 2, 3) and self.names[p] is not None:
                    self.log.append("%s left - a bot takes over" % self.names[p][:12])
                    self.chat_add(None, "%s left the game" % self.names[p][:12], MUTED)
                    self.names[p] = None
            elif t == "resync":
                g = self.rebuild(msg)
                if g:
                    self.next_game = g            # later messages are read by the rebuilt game
                    return
            else:
                self.inq.append(msg)
        if self.next_game or self.anim or now < self.pause_until or not self.inq:
            return
        msg = self.inq.popleft()
        t = msg.get("type")
        if t == "move":
            try:
                p, mv = msg["p"], tuple(int(x) for x in msg["m"])
            except (KeyError, TypeError, ValueError):
                return
            if self.result or self.resync_wait:
                return
            if p == self.b.turn and self.legal_ok(mv):
                self.play(mv)
            else:                                              # boards disagree: ask the host for its history
                self.resync_wait = True
                self.host.send({"type": "resync_req"})
                self.log.append("Re-syncing with the host...")
        elif t == "resign" and not self.resync_wait:
            p = msg.get("p")
            if p in (0, 1, 2, 3):
                self.resign_seat(p)
        elif t == "start":                                     # the host started a rematch
            names = msg.get("names")
            if isinstance(names, list) and len(names) == 4:
                self.next_game = NetGame4P(self.g, self.variant, self.teams, int(msg.get("elo", self.elo)),
                                           self.human, names, host=self.host)
                self.next_game.inherit_chat(self)

    # buttons
    def buttons(self):
        btns = [("Menu", pygame.Rect(760, 650, 100, 40)), ("Resign", pygame.Rect(760, 700, 100, 40)),
                ("Speed: 4x" if self.fast else "Speed: 1x", pygame.Rect(870, 700, 100, 40))]
        if self.is_hub:
            btns.insert(1, ("Rematch", pygame.Rect(870, 650, 100, 40)))
        return btns

    def press(self, label):
        if label == "Rematch":
            if self.result and self.is_hub:
                names = [self.names[s] if (s == self.human or s in self.peers) else None for s in range(4)]
                self.broadcast({"type": "start", "names": names, "elo": self.elo})
                self.next_game = NetGame4P(self.g, self.variant, self.teams, self.elo, self.human, names,
                                           peers=dict(self.peers))
                self.next_game.inherit_chat(self)
            return label
        return super().press(label)


class SpecViewMixin:
    """A read-only game fed by a player's spectator stream."""
    HINT = "You're spectating - go back to leave"
    back_to = "lan"
    chat_readonly = True

    def spec_view_init(self, peer):
        self.peer = peer
        self.squeue = deque()
        self.next_game = None
        self.chat_init()

    def replay(self, events, result):
        self.replaying = True
        for ev in events:
            if not self.apply_ev(ev):
                break
        self.replaying = False
        self.anim, self.choice = None, None
        if hasattr(self, "pause_until"):
            self.pause_until, self.banner = 0.0, None
            self.fade = {k: 0.0 for k in self.fade}
        if result and not self.result:
            self.result = result

    def click(self, pos):
        pass                                          # watching only (planning arrows still work)

    def send_chat(self, msg, team):
        self.chat_add(None, "Spectators can't send messages", MUTED)

    def close(self):
        self.peer.close()

    def spec_read(self):
        while True:
            msg = self.peer.get()
            if msg is None:
                return
            t = msg.get("type")
            if t == "spec":
                self.squeue.append(msg.get("ev"))
            elif t == "spec_chat":
                col = msg.get("color")
                col = tuple(col) if isinstance(col, list) and len(col) == 3 else TEXT
                who = msg.get("who")
                text_ = clean_chat(msg.get("text", ""))
                if text_:
                    self.chat_add(str(who)[:12] if who else None, text_, col)
            elif t == "spec_start":                   # the players started a rematch (or a re-sync)
                g = make_spectator(self.g, msg, self.peer)
                if g:
                    g.chat, g.tab, g.unread = self.chat, self.tab, self.unread
                    self.next_game = g
                    return
            elif t == "spec_end":
                self.chat_add(None, str(msg.get("text", "The game ended"))[:80], MUTED)
            elif t == "_closed":
                self.conn_lost = True             # shown once the moves already received have played out

    def spec_update(self):
        self.spec_read()
        if getattr(self, "conn_lost", False) and not self.squeue and not self.result and not self.anim:
            self.result = "Lost the connection to the game"
        if self.next_game or self.animating() or time.time() < getattr(self, "pause_until", 0) or not self.squeue:
            return
        if not self.apply_ev(self.squeue.popleft()) and not self.result:
            self.result = "Lost sync with the game"

    def buttons(self):
        return [("Menu", pygame.Rect(760, 650, 100, 40))] + self.extra_buttons()


class SpecGame2P(SpecViewMixin, ChatMixin, Game2P):
    def __init__(self, glyphs, info, peer):
        super().__init__(glyphs, info["variant"], ELOS[0], 1)
        self.spec_view_init(peer)
        self.white, self.black = str(info.get("white", "?"))[:12], str(info.get("black", "?"))[:12]
        self.me_label, self.opp_label = "White", "Black"
        self.title += " (watching)"
        clock = info.get("clock") or {}
        for k, side in (("1", 1), ("-1", -1)):
            if isinstance(clock.get(k), (int, float)):
                self.clock[side] = float(clock[k])

    def subtitle(self):
        return "%s vs %s" % (self.white, self.black)

    def side_text(self):
        return "Spectating: %s is White" % self.white

    def status_text(self):
        if self.result:
            return "Game over"
        side = "White" if self.board.turn == 1 else "Black"
        return ("%s in check" if self.board.in_check() else "%s to move") % side

    def apply_ev(self, ev):
        try:
            if ev[0] == "m":
                mv = tuple(int(x) for x in ev[1])
                if self.result or not move_ok(mv, self.legal, PROMO_KIND, 4):
                    return bool(self.result)
                self.play(mv)
                clock = ev[2] if len(ev) > 2 else {}
                for k, side in (("1", 1), ("-1", -1)):
                    if isinstance(clock.get(k), (int, float)):
                        self.clock[side] = float(clock[k])
            elif ev[0] == "end":
                if not self.result:
                    self.result = str(ev[1])[:60]
            return True
        except (IndexError, TypeError, ValueError, AttributeError):
            return False

    def update(self):
        now = time.time()
        dt, self.tick = now - self.tick, now
        self.spec_update()
        if self.blitz and not self.result and not self.animating():
            t = self.board.turn
            self.clock[t] = max(0.0, self.clock[t] - dt)     # display only; the players' clocks decide

    def extra_buttons(self):
        return [("Flip board", pygame.Rect(870, 650, 100, 40))]


class SpecGame4P(SpecViewMixin, ChatMixin, Game4P):
    def __init__(self, glyphs, info, peer):
        v = info["variant"]
        super().__init__(glyphs, int(info.get("elo", 900)), "military" if v in ("4pmil", "4pfull") else "standard",
                         v in ("4parmy", "4pfull"), bool(info.get("teams")))
        self.spec_view_init(peer)
        self.variant = v
        self.human, self.rot = -1, 0
        names = info.get("names")
        self.names = [str(n)[:10] if n else None for n in names] if isinstance(names, list) and len(names) == 4 \
            else [None] * 4
        self.title += " (watching)"

    def subtitle(self):
        return "Spectating - " + ("Teams 2v2" if self.teams else "Free-for-all")

    def player_name(self, p):
        return self.names[p] or PLAYER_NAMES[p] + " bot"

    def seat_label(self, p):
        return self.player_name(p) + ("" if self.b.alive[p] else " (out)")

    def finish(self):
        super().finish()
        self.result = self.result_neutral

    def apply_ev(self, ev):
        try:
            if ev[0] == "m":
                p, mv = int(ev[1]), tuple(int(x) for x in ev[2])
                if self.result:
                    return True
                if p != self.b.turn or not move_ok(mv, self.legal, PROMO4, 1):
                    return False
                self.play(mv)
            elif ev[0] == "r":
                self.resign_seat(int(ev[1]))
            elif ev[0] == "end":
                if not self.result:
                    self.result = str(ev[1])[:60]
            return True
        except (IndexError, TypeError, ValueError):
            return False

    def update(self):
        self.spec_update()

    def extra_buttons(self):
        return [("Speed: 4x" if self.fast else "Speed: 1x", pygame.Rect(870, 650, 100, 40))]


def make_spectator(glyphs, msg, peer):
    """Build the spectator view from a player's spec_start snapshot."""
    try:
        info = msg["info"]
        if info.get("kind") == 2 and info.get("variant") in LAN_VARIANTS:
            g = SpecGame2P(glyphs, info, peer)
        elif info.get("kind") == 4 and info.get("variant") in LAN4_VARIANTS:
            g = SpecGame4P(glyphs, info, peer)
        else:
            return None
        events = msg.get("events")
        g.replay(events if isinstance(events, list) else [], msg.get("result"))
        return g
    except (KeyError, TypeError, ValueError, AttributeError):
        return None


def describe_challenge(msg):
    v = msg["variant"]
    label = dict(VARIANTS)[v]
    if is4(v):
        seat, host = msg["seat"], msg.get("host_seat", 0)
        ally = msg.get("teams") and seat == (host + 2) % 4
        return "%s%s - you'd be %s%s (host is %s)" % (label, " 2v2" if msg.get("teams") else "", PLAYER_NAMES[seat],
                                                      ", their ally" if ally else "", PLAYER_NAMES[host])
    return "%s - you'd play %s" % (label, "White" if msg["host_side"] == 1 else "Black")


def valid_challenge(msg):
    if msg.get("type") != "challenge" or msg.get("proto") != NET_PROTO:
        return False
    v = msg.get("variant")
    if v in LAN_VARIANTS:
        return msg.get("host_side") in (1, -1)
    return v in LAN4_VARIANTS and msg.get("seat") in (0, 1, 2, 3) and msg.get("host_seat") in (0, 1, 2, 3) \
        and msg["seat"] != msg["host_seat"]


def my_name():
    try:
        return socket.gethostname()[:20] or "Player"
    except OSError:
        return "Player"


ERR = (220, 120, 90)


class Slot:
    """One outgoing challenge (one opponent's IP address)."""

    def __init__(self):
        self.text = ""
        self.peer = None
        self.state = ""            # "" | connecting | waiting | accepted | declined | failed
        self.name = ""
        self.note = ""

    def reset(self, keep_peer=False):
        if self.peer and not keep_peer:
            self.peer.close()
        self.peer, self.state, self.name, self.note = None, "", "", ""


class Lobby:
    """The LAN Play screen: type up to 1 (2-player) or 3 (4 Player) IP addresses and send challenges."""
    INPUT_X, INPUT_W = 250, 380
    CHALLENGE = pygame.Rect(250, 470, 190, 50)
    CANCEL = pygame.Rect(460, 470, 170, 50)
    START_BOTS = pygame.Rect(650, 470, 250, 50)
    BACK = pygame.Rect(80, 680, 200, 50)
    INBOX = pygame.Rect(300, 680, 240, 50)
    WATCH_INPUT = pygame.Rect(250, 584, 380, 44)
    WATCH_BTN = pygame.Rect(650, 584, 190, 44)

    def __init__(self, app):
        self.app = app
        self.slots = [Slot() for _ in range(3)]
        self.watch = Slot()         # "watch a game": the address of any player in that game
        self.focus = 0
        self.active = False         # challenges are out
        self.c_variant, self.c_teams, self.c_side, self.c_seat = None, False, 1, 0
        self.status, self.status_color = "", MUTED
        self.connect_q = queue.Queue()
        self.name = my_name()

    def say(self, msg, color=MUTED):
        self.status, self.status_color = msg, color

    def four(self):
        return is4(self.c_variant if self.active else self.app.variant)

    def n_slots(self):
        return 3 if self.four() else 1

    def input_rect(self, i):
        return pygame.Rect(self.INPUT_X, 262 + i * 62, self.INPUT_W, 48)

    def seat_of(self, i):
        """Slot i is the seat i+1 places after the host's own seat (so slot 1 is always the ally)."""
        return (self.c_seat + i + 1) % 4

    def slot_label(self, i):
        if not self.four():
            return "Opponent", TEXT
        teams = self.c_teams if self.active else self.app.teams
        ally = " (ally)" if teams and i == 1 else ""
        if not self.active and self.app.side4 == "random":
            return ("Ally" if ally else "Opponent") if teams else "Player %d" % (i + 2), DEAD_COLOR
        seat = self.seat_of(i) if self.active else i + 1
        return PLAYER_NAMES[seat] + ally, PLAYER_COLORS[seat]

    # sending
    def challenge(self):
        if self.active:
            return
        n = self.n_slots()
        used = [i for i in range(n) if self.slots[i].text.strip()]
        if not used:
            self.say("Type an IP address first." if n == 1 else "Type at least one IP address.", ERR)
            return
        addrs = {}
        for i in used:
            try:
                addrs[i] = parse_address(self.slots[i].text)
            except ValueError:
                self.say("Bad address: %s  (use an IP like 192.168.1.20, optionally :port)"
                         % self.slots[i].text.strip(), ERR)
                return
        self.active = True
        self.c_variant = self.app.variant
        self.c_teams = self.app.teams and is4(self.c_variant)
        side = self.app.side if self.app.side != "random" else random.choice(("white", "black"))
        self.c_side = 1 if side == "white" else -1
        self.c_seat = random.randrange(4) if self.app.side4 == "random" else 0
        for s in self.slots:
            s.reset()
        self.say("Sending challenge%s..." % ("s" if len(used) > 1 else ""))
        for i, (host, port) in addrs.items():
            self.slots[i].state, self.slots[i].note = "connecting", "Connecting..."
            threading.Thread(target=self._connect, args=(i, host, port), daemon=True).start()

    def _connect(self, i, host, port):
        try:
            self.connect_q.put((i, True, socket.create_connection((host, port), timeout=5), (host, port)))
        except OSError as exc:
            self.connect_q.put((i, False, exc, (host, port)))

    def cancel(self, status="Challenge cancelled."):
        for s in self.slots:
            if s.peer:
                s.peer.send({"type": "cancel"})
            s.reset()
        self.active = False
        self.say(status if status else "")

    def challenge_msg(self, i):
        msg = {"type": "challenge", "proto": NET_PROTO, "name": self.name, "variant": self.c_variant}
        if is4(self.c_variant):
            msg.update(seat=self.seat_of(i), host_seat=self.c_seat, teams=self.c_teams)
        else:
            msg["host_side"] = -self.c_side
        return msg

    # per-frame
    # watching
    def start_watch(self):
        w = self.watch
        if w.state:
            return
        try:
            host, port = parse_address(w.text)
        except ValueError:
            host = ""
        if not host:
            self.say("Type the address of a player in the game you want to watch.", ERR)
            return
        w.state = "connecting"
        self.say("Connecting to %s:%d to watch..." % (host, port))
        threading.Thread(target=self._connect, args=("w", host, port), daemon=True).start()

    def stop_watch(self, status=None, color=MUTED):
        self.watch.reset()
        if status is not None:
            self.say(status, color)

    def pump_watch(self):
        w = self.watch
        while w.peer:
            msg = w.peer.get()
            if msg is None:
                break
            t = msg.get("type")
            if t == "spec_start":
                g = make_spectator(self.app.glyphs, msg, w.peer)
                if g is None:
                    self.stop_watch("Couldn't read that game (different game version?)", ERR)
                    return
                w.reset(keep_peer=True)
                self.say("")
                self.app.inbox.decline_all()
                self.app.begin_net_game(g)
                return
            if t == "decline":
                self.stop_watch("Can't watch: %s." % (msg.get("reason") or "declined"), ERR)
            elif t == "_closed":
                self.stop_watch("Can't watch: the connection was closed.", ERR)

    def pump(self):
        while True:
            try:
                i, ok, res, (host, port) = self.connect_q.get_nowait()
            except queue.Empty:
                break
            if i == "w":
                if self.watch.state != "connecting":
                    if ok:
                        res.close()
                elif not ok:
                    short, why = connect_error(res)
                    self.stop_watch("%s: %s (%s)" % (host, short, why), ERR)
                else:
                    res.settimeout(None)
                    self.watch.peer, self.watch.state = Peer(res, (host, port)), "waiting"
                    self.watch.peer.send({"type": "spectate", "proto": NET_PROTO, "name": self.name})
                    self.say("Asking to watch %s's game..." % host)
                continue
            slot = self.slots[i]
            if not self.active or slot.state != "connecting":     # cancelled meanwhile
                if ok:
                    res.close()
                continue
            if not ok:
                short, why = connect_error(res)
                slot.state, slot.note = "failed", short
                self.say("%s: %s (%s)" % (host, short, why), ERR)
                continue
            res.settimeout(None)
            slot.peer, slot.state, slot.note = Peer(res, (host, port)), "waiting", "Waiting for answer..."
            slot.peer.send(self.challenge_msg(i))
        self.pump_watch()
        if not self.active:
            return
        for i, slot in enumerate(self.slots):
            while slot.peer:
                msg = slot.peer.get()
                if msg is None:
                    break
                t = msg.get("type")
                if t == "accept" and slot.state == "waiting":
                    slot.state, slot.name = "accepted", str(msg.get("name") or slot.peer.addr)[:20]
                    slot.note = "Accepted - " + slot.name
                    if not self.four():
                        self.start2(slot)
                        return
                elif t == "decline":
                    reason = msg.get("reason") or "declined"
                    slot.reset()
                    slot.state, slot.note = "declined", "Busy" if reason == "busy" else \
                        ("Left" if reason == "left" else "Declined")
                    if not self.four():
                        self.cancel("Challenge declined (%s)." % ("they are busy" if reason == "busy" else reason))
                        self.status_color = ERR
                        return
                elif t == "_closed":
                    slot.reset()
                    slot.state, slot.note = "failed", "Hung up"
                    if not self.four():
                        self.cancel("The other player hung up.")
                        return
        n = self.n_slots()
        states = [self.slots[i].state for i in range(n) if self.slots[i].state]
        if not self.four():
            if states and all(st == "failed" for st in states):
                self.active = False
            return
        if any(st in ("connecting", "waiting") for st in states):
            return
        acc = states.count("accepted")
        if acc and acc == len(states):
            self.start4()
        elif acc:
            self.say("Not everyone accepted - start with bots in the empty seats, or cancel.")
        else:
            self.cancel("Nobody accepted the challenge.")
            self.status_color = ERR

    def start2(self, slot):
        game = NetGame2P(self.app.glyphs, self.c_variant, self.c_side, slot.peer, slot.name, back_to="lan")
        slot.reset(keep_peer=True)
        self.cancel("")
        self.app.begin_net_game(game)

    def start4(self):
        names, peers = [None] * 4, {}
        names[self.c_seat] = self.name
        for i, slot in enumerate(self.slots):
            if slot.state == "accepted" and slot.peer and slot.peer.alive:
                names[self.seat_of(i)], peers[self.seat_of(i)] = slot.name, slot.peer
        for pr in peers.values():
            pr.send({"type": "start", "names": names, "elo": self.app.elo})
        game = NetGame4P(self.app.glyphs, self.c_variant, self.c_teams, self.app.elo, self.c_seat, names, peers=peers)
        for slot in self.slots:
            slot.reset(keep_peer=slot.peer in peers.values())
        self.cancel("")
        self.app.begin_net_game(game)

    def ready_with_bots(self):
        if not (self.active and self.four()):
            return False
        st = [s.state for s in self.slots if s.state]
        return "accepted" in st and not any(x in ("connecting", "waiting") for x in st)

    # input
    def click(self, pos):
        if self.BACK.collidepoint(pos):
            self.cancel("")
            self.stop_watch()
            self.app.state = "menu"
            return
        if self.INBOX.collidepoint(pos):
            self.app.state = "challenges"
            return
        if self.WATCH_INPUT.collidepoint(pos):
            self.focus = "w"
            return
        if self.WATCH_BTN.collidepoint(pos):
            if self.watch.state:
                self.stop_watch("Stopped.")
            else:
                self.focus = "w"
                self.start_watch()
            return
        if self.active:
            if self.CANCEL.collidepoint(pos):
                self.cancel()
            elif self.START_BOTS.collidepoint(pos) and self.ready_with_bots():
                self.start4()
            return
        for i in range(self.n_slots()):
            if self.input_rect(i).collidepoint(pos):
                self.focus = i
        if self.CHALLENGE.collidepoint(pos):
            self.challenge()

    def key(self, e):
        order = ([] if self.active else list(range(self.n_slots()))) + ["w"]
        if self.focus not in order:
            self.focus = order[0]
        if e.key == pygame.K_TAB:
            k = order.index(self.focus) + (-1 if e.mod & pygame.KMOD_SHIFT else 1)
            self.focus = order[k % len(order)]
            return
        watching = self.focus == "w"
        slot = self.watch if watching else self.slots[self.focus]
        if watching and self.watch.state:
            return
        if e.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
            self.start_watch() if watching else self.challenge()
        elif e.key == pygame.K_BACKSPACE:
            slot.text = slot.text[:-1]
        elif e.unicode and e.unicode.isprintable() and not e.unicode.isspace() and len(slot.text) < 40:
            slot.text += e.unicode

    # drawing
    def draw(self, s):
        s.fill(BG)
        text(s, "LAN PLAY", 72, (W // 2, 60), TEXT, center=True)
        inbox = self.app.inbox
        if inbox.listen_error:
            text(s, inbox.listen_error, 24, (80, 112), ERR)
        else:
            text(s, "Your address:  %s   (port %d)" % (inbox.myip, NET_PORT), 30, (80, 112), ACCENT)
            if inbox.other_ips:
                text(s, "also: " + ", ".join(inbox.other_ips), 20, (W - 80, 118), MUTED, right=True)
        v = self.c_variant if self.active else self.app.variant
        if is4(v):
            teams = self.c_teams if self.active else self.app.teams
            color = PLAYER_NAMES[self.c_seat] if self.active else \
                ("Red" if self.app.side4 == "red" else "a random color")
            what = "%s%s, you play %s" % (dict(VARIANTS)[v], " (Teams 2v2)" if teams else "", color)
        else:
            side = {1: "White", -1: "Black"}[self.c_side] if self.active else \
                {"white": "White", "black": "Black", "random": "a random color"}[self.app.side]
            what = "%s, you play %s" % (dict(VARIANTS)[v], side)
        text(s, "Your challenge:  " + what, 26, (80, 160), TEXT)
        text(s, "(change the variant%s in the main menu)" % (", color, teams and bot Elo" if is4(v) else " and side"), 20,
             (80, 188), MUTED)
        text(s, "Opponent's IP address" if not is4(v) else
             "IP addresses of the other players  (leave a seat empty for a bot)", 24, (80, 228), MUTED)
        n = self.n_slots()
        if self.focus != "w":
            self.focus = min(self.focus, n - 1)
        for i in range(n):
            slot, r = self.slots[i], self.input_rect(i)
            label, col = self.slot_label(i)
            if is4(v):
                pygame.draw.circle(s, col, (90, r.centery), 8)
            text(s, label, 26, (106 if is4(v) else 80, r.y + 14), TEXT)
            editing = not self.active and i == self.focus and self.focus != "w"
            pygame.draw.rect(s, (24, 22, 20), r, border_radius=8)
            pygame.draw.rect(s, ACCENT if editing else (68, 64, 60), r, 2, border_radius=8)
            caret = "|" if editing and int(time.time() * 2) % 2 else ""
            if slot.text or self.active:
                text(s, slot.text + caret, 30, (r.x + 12, r.y + 13))
            else:
                text(s, ("e.g. 192.168.1.20" if i == 0 else "(bot)" if is4(v) else "") + caret, 30,
                     (r.x + 12, r.y + 13), (100, 96, 90))
            if self.active and slot.note:
                col = ACCENT if slot.state == "accepted" else ERR if slot.state in ("declined", "failed") else MUTED
                text(s, slot.note, 22, (r.right + 16, r.y + 15), col)
            elif self.active and is4(v) and not slot.state:
                text(s, "Bot", 22, (r.right + 16, r.y + 15), MUTED)
        button(s, self.CHALLENGE, "Challenge", enabled=not self.active)
        if self.active:
            button(s, self.CANCEL, "Cancel")
        if self.ready_with_bots():
            button(s, self.START_BOTS, "Start with bots")
        if self.status:
            text(s, self.status, 24, (W // 2, 552), self.status_color, center=True)
        # watch a friend's game
        w, r = self.watch, self.WATCH_INPUT
        text(s, "Watch a game", 26, (80, r.y + 12), TEXT)
        editing = self.focus == "w" and not w.state
        pygame.draw.rect(s, (24, 22, 20), r, border_radius=8)
        pygame.draw.rect(s, ACCENT if editing else (68, 64, 60), r, 2, border_radius=8)
        caret = "|" if editing and int(time.time() * 2) % 2 else ""
        if w.text or editing:
            text(s, w.text + caret, 30, (r.x + 12, r.y + 11))
        else:
            text(s, "a player's address", 30, (r.x + 12, r.y + 11), (100, 96, 90))
        button(s, self.WATCH_BTN, "Stop" if w.state else "Watch")
        text(s, "Same game + same network for everyone. If nobody can reach you, allow Python / TCP port %d "
             "through your firewall." % NET_PORT, 19, (W // 2, 646), MUTED, center=True)
        button(s, self.BACK, "Back")
        inbox.draw_button(s, self.INBOX)


class Inbox:
    """Listens for challenges all the time and collects them for the Challenges screen."""
    MAX = 6
    ROW_Y, ROW_H = 165, 74
    BACK = pygame.Rect(80, 680, 200, 50)
    LAN = pygame.Rect(300, 680, 200, 50)
    HANDSHAKE_TIMEOUT = 10.0

    def __init__(self, app):
        self.app = app
        self.listener, self.listen_error = None, None
        self.entries = []           # {"peer", "msg" (None until the challenge arrives), "since"}
        self.joined = None          # a 4 Player challenge we accepted: waiting for the host to start
        self.toast = None
        self.myip = local_ip()
        self.other_ips = []
        self.unseen = 0
        self.name = my_name()

    def open(self):
        self.myip = local_ip()
        self.other_ips = [ip for ip in all_local_ips() if ip != self.myip][:3]
        if self.listener is None:
            try:
                self.listener = Listener()
                self.listen_error = None
            except OSError as exc:
                self.listen_error = "Can't receive challenges: port %d is in use (%s)" % (NET_PORT,
                                                                                          exc.strerror or exc)

    def ready(self):
        return [e for e in self.entries if e["msg"]]

    def remove(self, e, send=None):
        if send:
            e["peer"].send(send)
        e["peer"].close()
        if e in self.entries:
            self.entries.remove(e)
        if e is self.joined:
            self.joined = None

    def decline_all(self, keep=None):
        for e in list(self.entries):
            if e is not keep:
                self.remove(e, {"type": "decline", "reason": "busy"})

    def busy(self):
        a = self.app
        if a.tclient or (a.td and a.td.phase != "setup"):
            return True
        return a.state == "game" and isinstance(a.game, (NetGame2P, NetGame4P, SpecGame2P, SpecGame4P))

    def spectate(self, e, msg):
        """Someone wants to watch the LAN game we are playing."""
        g = self.app.game if self.app.state == "game" else None
        who = str(msg.get("name") or e["peer"].addr)[:20]
        if msg.get("proto") != NET_PROTO:
            self.remove(e, {"type": "decline", "reason": "different game version"})
        elif not isinstance(g, (NetGame2P, NetGame4P)):
            self.remove(e, {"type": "decline", "reason": "they aren't playing a LAN game right now"})
        elif len(g.specs) >= g.MAX_SPECS:
            self.remove(e, {"type": "decline", "reason": "too many spectators"})
        else:
            self.entries.remove(e)                  # the game owns this connection now
            g.add_spectator(e["peer"], who)
            self.toast = ("%s is watching your game" % who, time.time() + 4)

    def pump(self):
        if self.listener:
            while True:
                got = self.listener.get()
                if got is None:
                    break
                p = Peer(*got)
                if len(self.entries) >= self.MAX + 4:
                    p.send({"type": "decline", "reason": "busy"})
                    p.close()
                else:
                    self.entries.append({"peer": p, "msg": None, "since": time.time()})
        for e in list(self.entries):
            while e in self.entries:
                msg = e["peer"].get()
                if msg is None:
                    break
                t = msg.get("type")
                if e["msg"] is None:
                    if t == "spectate":
                        self.spectate(e, msg)
                    elif t in ("challenge", "t_invite") and (self.busy() or len(self.ready()) >= self.MAX):
                        self.remove(e, {"type": "decline", "reason": "busy"})
                    elif t == "t_invite" and valid_tinvite(msg):
                        e["msg"] = msg
                        who = str(msg.get("name") or e["peer"].addr)[:20]
                        self.toast = ("Tournament invite from %s - see Challenges" % who, time.time() + 6)
                        self.unseen += 1
                    elif t == "t_invite":
                        self.remove(e, {"type": "decline", "reason": "different game version"})
                    elif t == "challenge" and valid_challenge(msg):
                        e["msg"] = msg
                        who = str(msg.get("name") or e["peer"].addr)[:20]
                        self.toast = ("Challenge from %s - see Challenges" % who, time.time() + 6)
                        self.unseen += 1
                    elif t == "challenge":
                        self.remove(e, {"type": "decline", "reason": "different game version"})
                    elif t == "_closed":
                        self.remove(e)
                elif t in ("_closed", "cancel", "t_end"):
                    if e is self.joined:
                        self.toast = ("The host cancelled the 4 Player game", time.time() + 5)
                    self.remove(e)
                elif t == "start" and e is self.joined:
                    self.start4(e, msg)
                    return
            if e in self.entries and e["msg"] is None and time.time() - e["since"] > self.HANDSHAKE_TIMEOUT:
                self.remove(e)

    def accept(self, e):
        m = e["msg"]
        if m.get("type") == "t_invite":
            e["peer"].send({"type": "t_accept", "name": self.name})
            self.entries.remove(e)
            self.decline_all()
            self.app.tclient = TournamentClient(self.app, e["peer"], m)
            self.app.state = "tournament"
            return
        e["peer"].send({"type": "accept", "name": self.name})
        who = str(m.get("name") or e["peer"].addr)[:20]
        if is4(m["variant"]):
            self.joined = e
            return
        self.entries.remove(e)
        self.decline_all()
        self.app.begin_net_game(NetGame2P(self.app.glyphs, m["variant"], m["host_side"], e["peer"], who,
                                          back_to="challenges"))

    def start4(self, e, msg):
        m, names = e["msg"], msg.get("names")
        if not (isinstance(names, list) and len(names) == 4):
            self.remove(e)
            return
        self.entries.remove(e)
        self.joined = None
        self.decline_all()
        self.app.begin_net_game(NetGame4P(self.app.glyphs, m["variant"], bool(m.get("teams")),
                                          int(msg.get("elo", 900)), m["seat"], names, host=e["peer"]))

    # screen
    def rows(self):
        out = []
        for n, e in enumerate(self.ready()):
            y = self.ROW_Y + n * self.ROW_H
            out.append((e, pygame.Rect(80, y, 840, self.ROW_H - 8),
                        pygame.Rect(630, y + 12, 130, 42), pygame.Rect(775, y + 12, 130, 42)))
        return out

    def click(self, pos):
        if self.BACK.collidepoint(pos):
            self.app.state = "menu"
            return
        if self.LAN.collidepoint(pos):
            self.app.open_lobby()
            return
        for e, _, acc, dec in self.rows():
            if e is self.joined:
                if dec.collidepoint(pos):
                    self.remove(e, {"type": "decline", "reason": "left"})
            elif acc.collidepoint(pos) and not self.joined:
                self.accept(e)
                return
            elif dec.collidepoint(pos):
                self.remove(e, {"type": "decline", "reason": "declined"})

    def draw(self, s):
        s.fill(BG)
        text(s, "CHALLENGES", 72, (W // 2, 60), TEXT, center=True)
        if self.listen_error:
            text(s, self.listen_error, 24, (80, 112), ERR)
        else:
            text(s, "Others can challenge you at  %s   (port %d)" % (self.myip, NET_PORT), 28, (80, 112), ACCENT)
            if self.other_ips:
                text(s, "If that doesn't work, try: " + ", ".join(self.other_ips), 20, (80, 140), MUTED)
        self.unseen = 0
        rows = self.rows()
        if not rows:
            text(s, "No challenges yet.", 34, (W // 2, 300), MUTED, center=True)
            text(s, "Challenges sent to you will show up here, even while you play a bot.", 24, (W // 2, 340),
                 MUTED, center=True)
        for e, r, acc, dec in rows:
            m = e["msg"]
            joined = e is self.joined
            pygame.draw.rect(s, (24, 22, 20), r, border_radius=10)
            pygame.draw.rect(s, ACCENT if joined else (68, 64, 60), r, 2, border_radius=10)
            text(s, "%s  (%s)" % (str(m.get("name") or "Someone")[:20], e["peer"].addr), 28, (r.x + 16, r.y + 10))
            text(s, describe_tinvite(m) if m.get("type") == "t_invite" else describe_challenge(m), 22,
                 (r.x + 16, r.y + 40), MUTED)
            if joined:
                text(s, "Joined - waiting for the host...", 22, (acc.right - 6, acc.y + 12), ACCENT, right=True)
                button(s, dec, "Leave")
            else:
                button(s, acc, "Accept", enabled=not self.joined)
                button(s, dec, "Decline")
        button(s, self.BACK, "Back")
        button(s, self.LAN, "LAN Play")

    def draw_button(self, s, rect):
        n = len(self.ready())
        button(s, rect, "Challenges (%d)" % n if n else "Challenges", selected=n > 0)

    def draw_toast(self, s):
        if not self.toast or time.time() > self.toast[1]:
            n = len(self.ready())
            if self.unseen and n:              # stays in the top margin until the Challenges screen is opened
                text(s, "%d new challenge%s - open Challenges from the menu" % (n, "s" if n > 1 else ""), 18,
                     (22, 3), ACCENT)
            return
        img = font(26).render(self.toast[0], True, TEXT)
        box = img.get_rect(midtop=(W // 2, 8)).inflate(32, 18)
        pygame.draw.rect(s, (24, 22, 20), box, border_radius=10)
        pygame.draw.rect(s, ACCENT, box, 2, border_radius=10)
        s.blit(img, img.get_rect(center=box.center))


# ----------------------------------------------------------------------------
# Tournaments: single elimination, up to 4 rounds, run entirely on the organizer's computer
# ----------------------------------------------------------------------------
# Every player keeps ONE connection to the organizer.  Matches are played on the organizer's machine
# (Relay2P for 2-player games, a screen-less NetGame4P hub for 4 Player), and each player's game or
# spectator view talks to it through a numbered "channel" on that connection:
#   {"type": "g", "c": channel, "d": <normal LAN game message>}    {"type": "g_close", "c": channel}
# Control messages: t_invite / t_accept / t_state / t_match / t_watch / t_watching / t_end.
T_MAX_ROUNDS = 4
T_SWITCH_DELAY = 4.0        # seconds between the last result of a round and the next round starting


def t_layout(variant, teams):
    """(players per match, players who advance from each match, max rounds)."""
    if not is4(variant):
        return 2, 1, 4
    if teams:
        return 4, 2, 4                  # the winning pair moves on together
    return 4, 1, 2                      # free-for-all: 3 rounds would need 64 players


def t_round_sizes(variant, teams, rounds):
    """Number of players in each round."""
    k, adv, _ = t_layout(variant, teams)
    sizes = [k]
    for _ in range(rounds - 1):
        sizes.insert(0, sizes[0] * k // adv)
    return sizes


def _copy(msg):
    return json.loads(json.dumps(msg))


class PipeEnd:
    """In-process stand-in for a Peer (the organizer's own game talking to a match on the same computer)."""
    addr = "this computer"

    def __init__(self):
        self.q, self.other, self.closed = deque(), None, False

    @property
    def alive(self):
        return not self.closed

    def send(self, msg):
        if not self.closed and self.other and not self.other.closed:
            self.other.q.append(_copy(msg))

    def get(self):
        return self.q.popleft() if self.q else None

    def close(self):
        if not self.closed:
            self.closed = True
            if self.other and not self.other.closed:
                self.other.closed = True
                self.other.q.append({"type": "_closed"})


def pipe_pair():
    a, b = PipeEnd(), PipeEnd()
    a.other, b.other = b, a
    return a, b


class VirtualPeer:
    """One channel multiplexed over a real Peer connection; looks like a Peer to the games."""

    def __init__(self, conn, cid):
        self.conn, self.cid, self.addr = conn, cid, conn.addr
        self.q, self.closed = deque(), False

    @property
    def alive(self):
        return not self.closed and self.conn.alive

    def send(self, msg):
        if self.alive:
            self.conn.send({"type": "g", "c": self.cid, "d": msg})

    def get(self):
        return self.q.popleft() if self.q else None

    def feed(self, msg):
        if msg.get("type") == "_closed":
            if self.closed:
                return
            self.closed = True
        self.q.append(msg)

    def close(self):
        if not self.closed:
            self.closed = True
            if self.conn.alive:
                self.conn.send({"type": "g_close", "c": self.cid})


def route_channel_msg(routes, msg):
    """Deliver a g / g_close message to its channel.  Returns True if it was one."""
    t = msg.get("type")
    if t == "g":
        vp = routes.get(msg.get("c"))
        if vp and isinstance(msg.get("d"), dict):
            vp.feed(msg["d"])
        return True
    if t == "g_close":
        vp = routes.get(msg.get("c"))
        if vp:
            vp.feed({"type": "_closed"})
        return True
    return False


def build_client_game(glyphs, info, peer):
    """The game screen for a tournament match (used by remote players and by the organizer)."""
    if info["kind"] == 2:
        g = NetGame2P(glyphs, info["variant"], int(info["side"]), peer, str(info.get("opp") or "?")[:20],
                      back_to="tournament")
    else:
        g = NetGame4P(glyphs, info["variant"], bool(info.get("teams")), int(info.get("elo", 900)), int(info["seat"]),
                      list(info["names"]), host=peer)
        g.back_to = "tournament"
    g.tournament = True
    g.HINT = "Tournament match over - Menu goes back to the bracket"
    return g


class Relay2P:
    """A 2-player tournament match run by the organizer.  Humans connect to it exactly as they would to a LAN
    opponent (it forwards each side's moves to the other); bot sides are played here."""
    MAX_PLIES = 400
    BOT_DELAY, BOT_DELAY_ALL_BOTS = 0.3, 0.75      # seconds; all-bot games are paced so spectators can follow

    def __init__(self, td, match, white, black):
        self.td, self.match, self.variant = td, match, td.v
        self.board = Board({"military": "military", "army": "army", "fullarmy": "fullarmy"}.get(td.v, "normal"))
        self.legal = self.board.legal()
        self.players = {1: white, -1: black}
        self.ends = {1: None, -1: None}
        self.blitz = td.v == "blitz"
        self.clock = {1: 180.0, -1: 180.0}
        self.tick = time.time()
        self.events, self.specs = [], []
        self.result, self.winner, self.bot = None, None, None

    def name(self, s):
        return self.players[s].label()

    def color(self, s):
        return "White" if s == 1 else "Black"

    def start(self):
        for s in (1, -1):
            if self.players[s].is_human():
                self.ends[s] = self.td.join(self.players[s], {"kind": 2, "variant": self.variant, "side": s,
                                                              "opp": self.name(-s)})

    def forward(self, s, msg):
        if self.ends[s]:
            self.ends[s].send(msg)

    # spectators
    def spec_info(self):
        return {"kind": 2, "variant": self.variant, "white": self.name(1), "black": self.name(-1),
                "clock": {"1": round(self.clock[1], 2), "-1": round(self.clock[-1], 2)}}

    def add_spectator(self, end, name):
        end.send({"type": "spec_start", "info": self.spec_info(), "events": self.events, "result": self.result})
        self.specs.append(end)

    def spec_send(self, msg):
        for e in self.specs:
            e.send(msg)

    def spec_pump(self):
        for e in list(self.specs):
            while True:
                m = e.get()
                if m is None or m.get("type") == "_closed":
                    break
            if not e.alive:
                self.specs.remove(e)

    # game
    def apply(self, mv):
        b = self.board
        mover = b.turn
        b.make(mv)
        b.history.append(b.key())
        self.legal = b.legal()
        ev = ["m", list(mv), {"1": round(self.clock[1], 2), "-1": round(self.clock[-1], 2)}]
        self.events.append(ev)
        self.spec_send({"type": "spec", "ev": ev})
        if not self.legal:
            if b.in_check():
                self.finish(mover, "Checkmate")
            else:
                self.draw("stalemate")
        elif b.halfmove >= 100:
            self.draw("50-move rule")
        elif b.history.count(b.key()) >= 3:
            self.draw("repetition")
        elif not b.military and b.insufficient():
            self.draw("insufficient material")
        elif len(self.events) >= self.MAX_PLIES:              # very long game: decide on material
            sc = b.evaluate()
            if sc == 0:
                self.draw("move limit")
            else:
                self.finish(1 if sc > 0 else -1, "On material")

    def draw(self, why):
        self.finish(-1, "Draw (%s) - Black advances" % why)

    def finish(self, winner, why):
        if self.result:
            return
        self.winner = winner
        self.result = why if why.startswith("Draw") else "%s - %s wins" % (why, self.color(winner))
        self.spec_send({"type": "spec", "ev": ["end", self.result]})
        self.td.match_done(self.match, [self.players[winner].slot], self.result)

    def on_msg(self, s, msg):
        t = msg.get("type")
        if t == "move":
            if self.result or self.board.turn != s:
                return
            try:
                mv = tuple(int(x) for x in msg["m"])
            except (KeyError, TypeError, ValueError):
                return
            if not move_ok(mv, self.legal, PROMO_KIND, 4):
                return
            if isinstance(msg.get("clock"), (int, float)):
                self.clock[s] = float(msg["clock"])
            self.forward(-s, msg)
            self.apply(mv)
        elif t in ("resign", "timeout", "_closed"):
            if not self.result:
                self.forward(-s, {"type": "timeout" if t == "timeout" else "resign"})
                self.finish(-s, "%s %s" % (self.color(s), {"resign": "resigned", "timeout": "ran out of time",
                                                           "_closed": "left"}[t]))
        elif t == "chat":
            text_ = clean_chat(msg.get("text", ""))
            if text_:
                self.forward(-s, {"type": "chat", "text": text_})
                self.spec_send({"type": "spec_chat", "who": self.name(s)[:12], "text": text_, "color": list(OPP_COLOR)})

    def pump(self):
        now = time.time()
        dt, self.tick = now - self.tick, now
        for s in (1, -1):
            e = self.ends[s]
            while e:
                msg = e.get()
                if msg is None:
                    break
                self.on_msg(s, msg)
        self.spec_pump()
        if self.result:
            return
        turn = self.board.turn
        if self.blitz:
            self.clock[turn] -= dt
            if self.clock[turn] < -(NetGame2P.FLAG_GRACE + 1):      # that player's client never reported it
                self.forward(-turn, {"type": "timeout"})
                self.finish(-turn, "%s ran out of time" % self.color(turn))
                return
        if self.ends[turn] is not None or self.players[turn].is_human():
            return                                            # waiting for a human
        if self.bot is None:
            b, elo = self.board.copy(), self.td.elo
            both_bots = self.ends[-turn] is None
            tl = min(LEVELS[elo][3], 0.4) if both_bots else LEVELS[elo][3]
            job = {"done": False, "move": None, "t0": now, "delay": self.BOT_DELAY_ALL_BOTS if both_bots else self.BOT_DELAY}

            def work():
                try:
                    job["move"] = choose_move(b, elo, tl)
                except Exception:
                    job["move"] = None
                job["done"] = True
            threading.Thread(target=work, daemon=True).start()
            self.bot = job
        elif self.bot["done"] and now - self.bot["t0"] > self.bot["delay"]:
            mv, self.bot = self.bot["move"], None
            if mv not in self.legal:
                mv = random.choice(self.legal)
            if self.blitz:
                self.clock[turn] += 2
            self.forward(-turn, {"type": "move", "m": list(mv), "clock": round(self.clock[turn], 2)})
            self.apply(mv)


def hub_winners(hub):
    """Who advances from a finished 4 Player match (seats).  Ties are settled by a coin toss."""
    b = hub.b
    if hub.teams:
        a, c = b.score[0] + b.score[2], b.score[1] + b.score[3]
        out0, out1 = not (b.alive[0] or b.alive[2]), not (b.alive[1] or b.alive[3])
        if out1 != out0:
            t = 0 if out1 else 1
        elif a != c:
            t = 0 if a > c else 1
        else:
            t = random.choice((0, 1))
        return [t, t + 2]
    top = max(b.score)
    return [random.choice([i for i in range(4) if b.score[i] == top])]


class TPlayer:
    def __init__(self, slot, kind, name, conn=None):
        self.slot, self.kind, self.name, self.conn = slot, kind, name, conn    # kind: you | remote | bot
        self.routes = {}                  # remote: channel id -> VirtualPeer
        self.watch_end = None             # the spectator channel this player is using, if any
        self.gone = False

    def is_human(self):
        return self.kind == "you" or (self.kind == "remote" and not self.gone)

    def label(self):
        if self.kind == "bot":
            return self.name
        return self.name + (" (left)" if self.gone else "")


class TMatch:
    def __init__(self, mid, rnd, slots):
        self.id, self.round, self.slots = mid, rnd, slots
        self.status, self.winners, self.note, self.server = "live", [], "", None
        self.seat_slot = None             # 4 Player: seat -> bracket slot


class TournamentDirector:
    """The organizer's side: invites players, builds the bracket, runs every match, streams spectators."""
    COLS, ROWS = 4, 8
    SLOT_W, SLOT_H = 200, 34

    def __init__(self, app):
        self.app = app
        self.phase = "setup"              # setup | inviting | running | done
        self.rounds = 2
        self.texts = [""] * 32
        self.me_playing = True
        self.focus = 1
        self.status, self.status_color = "", MUTED
        self.invites = {}                 # slot -> {"state", "peer", "name", "note"}
        self.connect_q = queue.Queue()
        self.players, self.matches = [], []
        self.me = TPlayer(None, "you", my_name())
        self.cid = 0
        self.round_done_at = None
        self.champions = None
        self.cur_round = -1
        self.dirty = False

    # ---- setup -------------------------------------------------------------
    def teams(self):
        return self.app.teams and is4(self.app.variant)

    def max_rounds(self):
        return t_layout(self.app.variant, self.teams())[2]

    def n_players(self):
        self.rounds = max(1, min(self.rounds, self.max_rounds()))
        return t_round_sizes(self.app.variant, self.teams(), self.rounds)[0]

    def say(self, msg, color=MUTED):
        self.status, self.status_color = msg, color

    def slot_rect(self, i):
        return pygame.Rect(80 + (i // self.ROWS) * 215, 220 + (i % self.ROWS) * 40, self.SLOT_W, self.SLOT_H)

    ROUND_BTNS = [pygame.Rect(200 + n * 70, 128, 60, 36) for n in range(4)]
    ME_BTN = pygame.Rect(520, 128, 190, 36)
    SHUFFLE = pygame.Rect(730, 128, 170, 36)
    INVITE = pygame.Rect(250, 560, 230, 50)
    START = pygame.Rect(500, 560, 250, 50)
    CANCEL = pygame.Rect(770, 560, 130, 50)
    BACK = pygame.Rect(80, 680, 200, 50)

    def begin_invites(self):
        n = self.n_players()
        self.v, self.tm, self.elo = self.app.variant, self.teams(), self.app.elo
        self.invites = {}
        for i in range(n):
            if self.me_playing and i == 0:
                continue
            txt = self.texts[i].strip()
            if not txt:
                continue
            try:
                host, port = parse_address(txt)
            except ValueError:
                self.say("Slot %d: bad address '%s'" % (i + 1, txt), ERR)
                return
            self.invites[i] = {"state": "connecting", "peer": None, "name": "", "note": "Connecting..."}
            threading.Thread(target=self._connect, args=(i, host, port), daemon=True).start()
        self.phase = "inviting"
        self.say("Sending invitations..." if self.invites else "No addresses - starting with bots only.")

    def _connect(self, i, host, port):
        try:
            self.connect_q.put((i, True, socket.create_connection((host, port), timeout=5)))
        except OSError as exc:
            self.connect_q.put((i, False, exc))

    def cancel_invites(self):
        for inv in self.invites.values():
            if inv["peer"]:
                inv["peer"].send({"type": "t_end", "reason": "The organizer cancelled the tournament"})
                inv["peer"].close()
        self.invites = {}
        self.phase = "setup"
        self.say("Cancelled.")

    def pending(self):
        return any(inv["state"] in ("connecting", "waiting") for inv in self.invites.values())

    def pump_invites(self):
        while True:
            try:
                i, ok, res = self.connect_q.get_nowait()
            except queue.Empty:
                break
            inv = self.invites.get(i)
            if not inv or inv["state"] != "connecting":
                if ok:
                    res.close()
                continue
            if not ok:
                inv["state"], inv["note"] = "failed", connect_error(res)[0]
                continue
            res.settimeout(None)
            inv["peer"], inv["state"], inv["note"] = Peer(res, res.getpeername()), "waiting", "Waiting..."
            inv["peer"].send({"type": "t_invite", "proto": NET_PROTO, "name": self.me.name, "variant": self.v,
                              "teams": self.tm, "rounds": self.rounds, "slot": i, "players": self.n_players()})
        for i, inv in self.invites.items():
            p = inv["peer"]
            while p and inv["state"] in ("waiting", "accepted"):
                msg = p.get()
                if msg is None:
                    break
                t = msg.get("type")
                if t == "t_accept" and inv["state"] == "waiting":
                    inv["state"], inv["name"] = "accepted", str(msg.get("name") or p.addr)[:16]
                    inv["note"] = "Joined - " + inv["name"]
                    p.send({"type": "t_state", "state": self.preview_state()})
                elif t in ("decline", "_closed"):
                    inv["state"], inv["note"] = "declined", "Left" if t == "_closed" else \
                        ("Busy" if msg.get("reason") == "busy" else "Declined")
                    p.close()
                    inv["peer"] = None
        if self.phase == "inviting" and not self.pending():
            if all(inv["state"] == "accepted" for inv in self.invites.values()):
                self.start()

    def preview_state(self):
        names = []
        for i in range(self.n_players()):
            inv = self.invites.get(i)
            if self.me_playing and i == 0:
                names.append(self.me.name)
            elif inv and inv["state"] == "accepted":
                names.append(inv["name"])
            elif inv and inv["state"] in ("connecting", "waiting"):
                names.append("(invited)")
            else:
                names.append("Bot %d" % (i + 1))
        return {"variant": self.v, "teams": self.tm, "rounds": self.rounds, "names": names, "matches": [],
                "champions": None, "phase": "waiting"}

    # ---- running -----------------------------------------------------------
    def start(self):
        self.players = []
        for i in range(self.n_players()):
            inv = self.invites.get(i)
            if self.me_playing and i == 0:
                self.me.slot = 0
                self.players.append(self.me)
            elif inv and inv["state"] == "accepted" and inv["peer"] and inv["peer"].alive:
                self.players.append(TPlayer(i, "remote", inv["name"], inv["peer"]))
            else:
                if inv and inv["peer"]:
                    inv["peer"].close()
                self.players.append(TPlayer(i, "bot", "Bot %d" % (i + 1)))
        if not self.me_playing:
            self.me.slot = None
        self.invites = {}
        self.phase = "running"
        self.say("")
        self.app.state = "tournament"         # (the organizer's own match, if any, takes over the screen)
        self.start_round(0)

    def remotes(self):
        return [p for p in self.players if p.kind == "remote" and not p.gone]

    def next_cid(self):
        self.cid += 1
        return self.cid

    def stop_watch(self, p):
        if p.watch_end:
            p.watch_end.close()
            p.watch_end = None

    def join(self, p, info):
        """Put player p into a match: returns the match server's end of their channel."""
        self.stop_watch(p)
        if p.kind == "you":
            a, b = pipe_pair()
            self.app.switch_game(build_client_game(self.app.glyphs, info, b))
            return a
        cid = self.next_cid()
        vp = VirtualPeer(p.conn, cid)
        p.routes[cid] = vp
        msg = dict(info)
        msg.update(type="t_match", c=cid)
        p.conn.send(msg)
        return vp

    def watch(self, p, mid):
        m = self.matches[mid] if isinstance(mid, int) and 0 <= mid < len(self.matches) else None
        if not m or m.status != "live":
            return
        if p.is_human() and p.slot is not None and any(x.status == "live" and p.slot in x.slots for x in self.matches):
            return                           # you're playing right now

        self.stop_watch(p)
        if p.kind == "you":
            a, b = pipe_pair()
            m.server.add_spectator(a, p.name)
            g = make_spectator(self.app.glyphs, b.get(), b)
            if g:
                g.back_to = "tournament"
                p.watch_end = a
                self.app.switch_game(g)
            return
        cid = self.next_cid()
        vp = VirtualPeer(p.conn, cid)
        p.routes[cid] = vp
        p.conn.send({"type": "t_watching", "c": cid})
        m.server.add_spectator(vp, p.label())
        p.watch_end = vp

    def start_round(self, r):
        k, adv, _ = t_layout(self.v, self.tm)
        if r == 0:
            entrants = list(range(len(self.players)))
        else:
            entrants = [s for m in self.matches if m.round == r - 1 for s in m.winners]
        self.cur_round, self.round_done_at = r, None
        for j in range(0, len(entrants), k):
            m = TMatch(len(self.matches), r, entrants[j:j + k])
            self.matches.append(m)
            self.start_match(m)
        self.dirty = True

    def start_match(self, m):
        ps = [self.players[s] for s in m.slots]
        if len(ps) == 2:
            if random.random() < 0.5:
                ps.reverse()
            m.server = Relay2P(self, m, ps[0], ps[1])
            m.server.start()
            return
        if self.tm:                        # slots [a1, a2, b1, b2]: pair a = Red + Yellow, pair b = Blue + Green
            pairs = [ps[:2], ps[2:]]
            random.shuffle(pairs)
            seats = [pairs[0][0], pairs[1][0], pairs[0][1], pairs[1][1]]
        else:
            seats = ps[:]
            random.shuffle(seats)
        m.seat_slot = [p.slot for p in seats]
        names = [p.label() for p in seats]
        peers = {}
        hub = NetGame4P(self.app.glyphs, self.v, self.tm, self.elo, -1, names, peers=peers)
        hub.tournament = True
        m.server = hub
        for seat, p in enumerate(seats):
            if p.is_human():
                peers[seat] = self.join(p, {"kind": 4, "variant": self.v, "teams": self.tm, "seat": seat,
                                            "names": names, "elo": self.elo})

    def match_done(self, m, winner_slots, note):
        if m.status == "done":
            return
        m.status, m.winners, m.note = "done", winner_slots, note
        self.dirty = True

    def pump(self):
        if self.phase in ("setup", "inviting"):
            self.pump_invites()
            return
        for p in self.remotes():
            while True:
                msg = p.conn.get()
                if msg is None:
                    break
                if route_channel_msg(p.routes, msg):
                    continue
                t = msg.get("type")
                if t == "t_watch":
                    self.watch(p, msg.get("match"))
                elif t == "_closed":
                    p.gone = True
                    for vp in p.routes.values():
                        vp.feed({"type": "_closed"})
                    self.dirty = True
                    break
        for m in self.matches:
            if m.server is None:
                continue
            if isinstance(m.server, Relay2P):
                m.server.pump()
            else:
                m.server.update()
                if m.server.result and m.status == "live":
                    self.match_done(m, [m.seat_slot[s] for s in hub_winners(m.server)],
                                    getattr(m.server, "result_neutral", None) or m.server.result)
        if self.phase == "running":
            live = [m for m in self.matches if m.round == self.cur_round and m.status == "live"]
            if not live:
                if self.cur_round == self.rounds - 1:
                    final = [m for m in self.matches if m.round == self.cur_round]
                    self.champions = [s for m in final for s in m.winners]
                    self.phase = "done"
                    self.dirty = True
                elif self.round_done_at is None:
                    self.round_done_at = time.time()
                elif time.time() - self.round_done_at > T_SWITCH_DELAY:
                    self.start_round(self.cur_round + 1)
        if self.dirty:
            self.dirty = False
            st = self.state()
            for p in self.remotes():
                p.conn.send({"type": "t_state", "state": st})

    def state(self):
        if self.phase in ("setup", "inviting"):
            return self.preview_state() if self.phase == "inviting" else None
        return {"variant": self.v, "teams": self.tm, "rounds": self.rounds,
                "names": [p.label() for p in self.players],
                "matches": [{"id": m.id, "round": m.round, "slots": m.slots, "status": m.status,
                             "winners": m.winners, "note": m.note} for m in self.matches],
                "champions": self.champions, "phase": "done" if self.phase == "done" else "running"}

    def shutdown(self, reason="The organizer ended the tournament"):
        if self.phase == "inviting":
            self.cancel_invites()
        for p in self.players:
            if p.kind == "remote" and not p.gone:
                p.conn.send({"type": "t_end", "reason": reason})
                p.conn.close()
        for m in self.matches:
            if isinstance(m.server, NetGame4P):
                m.server.spec_close()
        self.phase = "setup"

    # ---- setup screen --------------------------------------------------------
    def click(self, pos):
        app = self.app
        if self.BACK.collidepoint(pos):
            app.state = "menu"
            return
        if self.phase == "inviting":
            if self.CANCEL.collidepoint(pos):
                self.cancel_invites()
            elif self.START.collidepoint(pos) and not self.pending():
                self.start()
            return
        for n, r in enumerate(self.ROUND_BTNS):
            if r.collidepoint(pos) and n + 1 <= self.max_rounds():
                self.rounds = n + 1
        if self.ME_BTN.collidepoint(pos):
            self.me_playing = not self.me_playing
        if self.SHUFFLE.collidepoint(pos):
            n = self.n_players()
            start = 1 if self.me_playing else 0
            part = self.texts[start:n]
            random.shuffle(part)
            self.texts[start:n] = part
        for i in range(self.n_players()):
            if self.slot_rect(i).collidepoint(pos) and not (self.me_playing and i == 0):
                self.focus = i
        if self.INVITE.collidepoint(pos):
            self.begin_invites()

    def key(self, e):
        if self.phase != "setup":
            return
        n = self.n_players()
        order = [i for i in range(n) if not (self.me_playing and i == 0)]
        if self.focus not in order:
            self.focus = order[0]
        if e.key == pygame.K_TAB:
            k = order.index(self.focus) + (-1 if e.mod & pygame.KMOD_SHIFT else 1)
            self.focus = order[k % len(order)]
        elif e.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
            self.begin_invites()
        elif e.key == pygame.K_BACKSPACE:
            self.texts[self.focus] = self.texts[self.focus][:-1]
        elif e.unicode and e.unicode.isprintable() and not e.unicode.isspace() and len(self.texts[self.focus]) < 30:
            self.texts[self.focus] += e.unicode

    def draw(self, s):
        s.fill(BG)
        text(s, "TOURNAMENT", 64, (W // 2, 46), TEXT, center=True)
        v = self.v if self.phase == "inviting" else self.app.variant
        tm = self.tm if self.phase == "inviting" else self.teams()
        label = dict(VARIANTS)[v] + (" - Teams 2v2" if tm else "")
        rule = {2: "draws: Black advances", 4: "winning pair advances" if tm else "top score advances"}[
            4 if is4(v) else 2]
        text(s, "Game: %s   (bots Elo %d, %s)  - change in the main menu" % (label, self.app.elo, rule), 22,
             (80, 92), MUTED)
        n = self.n_players()
        text(s, "Rounds", 26, (80, 136), TEXT)
        setup = self.phase == "setup"
        for k, r in enumerate(self.ROUND_BTNS):
            button(s, r, str(k + 1), self.rounds == k + 1, enabled=setup and k + 1 <= self.max_rounds())
        button(s, self.ME_BTN, "I'm playing" if self.me_playing else "Just organizing", self.me_playing, enabled=setup)
        button(s, self.SHUFFLE, "Shuffle", enabled=setup)
        k = t_layout(v, tm)[0]
        text(s, "%d players - leave a box empty for a bot.  Boxes in the same color group play each other first%s."
             % (n, " (pairs = teams)" if tm else ""), 20, (80, 188), MUTED)
        for i in range(n):
            r = self.slot_rect(i)
            group = i // k
            tint = PLAYER_COLORS[group % 4]
            pygame.draw.rect(s, (24, 22, 20), r, border_radius=6)
            inv = self.invites.get(i)
            if inv:
                edge = ACCENT if inv["state"] == "accepted" else ERR if inv["state"] in ("failed", "declined") \
                    else MUTED
            else:
                edge = ACCENT if (setup and i == self.focus) else tuple(c // 2 for c in tint)
            pygame.draw.rect(s, edge, r, 2, border_radius=6)
            pygame.draw.rect(s, tint, (r.x - 6, r.y + 4, 3, r.h - 8))
            if tm and i % 2 == 0:
                pygame.draw.line(s, tint, (r.x - 6, r.y + 4), (r.x - 6, r.y + 2 * 40 - 10), 3)
            if self.me_playing and i == 0:
                text(s, "You (%s)" % self.me.name[:12], 20, (r.x + 8, r.y + 9), ACCENT)
                continue
            shown = inv["note"] if inv else self.texts[i]
            caret = "|" if setup and i == self.focus and int(time.time() * 2) % 2 else ""
            if shown or caret:
                text(s, (shown + caret)[-24:], 20, (r.x + 8, r.y + 9), TEXT if not inv else edge)
            else:
                text(s, "%d: bot" % (i + 1), 20, (r.x + 8, r.y + 9), (100, 96, 90))
        if setup:
            button(s, self.INVITE, "Send invites & start")
        else:
            if not self.pending():
                button(s, self.START, "Start (bots fill gaps)")
            button(s, self.CANCEL, "Cancel")
        if self.status:
            text(s, self.status, 22, (W // 2, 630), self.status_color, center=True)
        button(s, self.BACK, "Back")


class TournamentClient:
    """A player in someone else's tournament."""

    def __init__(self, app, conn, invite):
        self.app, self.conn = app, conn
        self.slot = int(invite.get("slot", 0))
        self.host_name = str(invite.get("name") or conn.addr)[:16]
        self.state = None
        self.routes = {}
        self.pending_spec = None
        self.ended = None

    def watch(self, mid):
        if not self.ended:
            self.conn.send({"type": "t_watch", "match": mid})

    def leave(self):
        self.app.drop_parked()
        self.conn.close()
        g = self.app.game
        if self.app.state == "game" and getattr(g, "back_to", "") == "tournament":
            g.dead = True
            g.close()
        self.app.tclient = None
        self.app.state = "menu"

    def pump(self):
        while True:
            msg = self.conn.get()
            if msg is None:
                break
            if route_channel_msg(self.routes, msg):
                continue
            t = msg.get("type")
            if t == "t_state" and isinstance(msg.get("state"), dict):
                self.state = msg["state"]
            elif t == "t_match":
                vp = VirtualPeer(self.conn, msg.get("c"))
                self.routes[msg.get("c")] = vp
                self.pending_spec = None
                try:
                    self.app.switch_game(build_client_game(self.app.glyphs, msg, vp))
                except (KeyError, TypeError, ValueError):
                    vp.close()
            elif t == "t_watching":
                vp = VirtualPeer(self.conn, msg.get("c"))
                self.routes[msg.get("c")] = vp
                self.pending_spec = vp
            elif t == "t_end":
                self.ended = str(msg.get("reason") or "The tournament ended")[:80]
            elif t == "_closed":
                if not self.ended:
                    self.ended = "Lost the connection to the organizer"
                for vp in self.routes.values():
                    vp.feed({"type": "_closed"})
        vp = self.pending_spec
        if vp and vp.q:
            msg = vp.get()
            self.pending_spec = None
            if msg.get("type") == "spec_start":
                g = make_spectator(self.app.glyphs, msg, vp)
                if g:
                    g.back_to = "tournament"
                    self.app.switch_game(g)
                    return
            vp.close()


def describe_tinvite(m):
    v = m["variant"]
    return "Tournament: %s%s - %d players, %d round%s" % (dict(VARIANTS)[v], " 2v2" if m.get("teams") else "",
                                                         m.get("players", 0), m["rounds"],
                                                         "s" if m["rounds"] > 1 else "")


def valid_tinvite(m):
    return m.get("proto") == NET_PROTO and (m.get("variant") in LAN_VARIANTS or m.get("variant") in LAN4_VARIANTS) \
        and m.get("rounds") in (1, 2, 3, 4) and isinstance(m.get("slot"), int)


class TournamentView:
    """The bracket screen (organizer and players).  Click a LIVE match to watch it."""
    BACK = pygame.Rect(80, 690, 200, 46)
    END = pygame.Rect(300, 690, 230, 46)
    RETURN = pygame.Rect(690, 690, 250, 46)
    TOP, BOTTOM = 150, 670

    def __init__(self, app):
        self.app = app

    def source(self):
        a = self.app
        if a.td and a.td.phase != "setup":
            return a.td.state(), a.td.me.slot, a.td.me.name, True
        if a.tclient:
            return a.tclient.state, a.tclient.slot, None, False
        return None, None, None, False

    def boxes(self, st):
        """(match id or None, rect, slots or None) for every bracket position."""
        sizes = t_round_sizes(st["variant"], st["teams"], st["rounds"])
        k = t_layout(st["variant"], st["teams"])[0]
        colw = (W - 80) // st["rounds"]
        out = []
        for r, size in enumerate(sizes):
            count = size // k
            ms = [m for m in st["matches"] if m["round"] == r]
            span = (self.BOTTOM - self.TOP) / count
            rh = min(18, int((span - 24) / k))
            h = rh * k + 8 + max(12, rh - 2)          # names + the result line
            for i in range(count):
                y = self.TOP + span * i + (span - h) / 2
                rect = pygame.Rect(40 + r * colw + 6, int(y), colw - 24, h)
                m = ms[i] if i < len(ms) else None
                out.append((m, rect, rh))
        return out

    def my_status(self, st, me):
        if st is None:
            return "Waiting for the organizer..."
        if st.get("champions"):
            names = " & ".join(st["names"][s] for s in st["champions"])
            if me is not None and me in st["champions"]:
                return "You won the tournament!"
            return "Champion: " + names
        if st.get("phase") == "waiting":
            return "Waiting for the organizer to start..."
        if me is None:
            return "Organizing - click a LIVE match to watch it"
        mine = [m for m in st["matches"] if me in m["slots"]]
        if mine and mine[-1]["status"] == "live":
            return "Your match is still going - press Return to my match" if self.app.parked else \
                "Your match is being played"
        if mine and me not in mine[-1]["winners"]:
            return "You're out - click a LIVE match to watch"
        return "You advance! Waiting for the next round - click a LIVE match to watch"

    def click(self, pos):
        a = self.app
        st, me, _, director = self.source()
        if self.BACK.collidepoint(pos):
            a.state = "menu"
            return
        if self.RETURN.collidepoint(pos) and a.parked:
            a.return_to_match()
            return
        if self.END.collidepoint(pos):
            if director:
                a.drop_parked()
                a.td.shutdown()
                a.td = None
            elif a.tclient:
                a.tclient.leave()
            a.state = "menu"
            return
        if not st:
            return
        if a.parked and not a.parked.result:
            return                           # finish (or return to) your own match first
        for m, rect, _ in self.boxes(st):
            if m and m["status"] == "live" and rect.collidepoint(pos):
                if director:
                    a.td.watch(a.td.me, m["id"])
                elif a.tclient:
                    a.tclient.watch(m["id"])

    def draw(self, s):
        s.fill(BG)
        a = self.app
        st, me, _, director = self.source()
        title = "TOURNAMENT"
        if st:
            title += " - " + dict(VARIANTS)[st["variant"]] + (" 2v2" if st["teams"] else "")
        text(s, title, 46, (W // 2, 40), TEXT, center=True)
        ended = a.tclient.ended if (a.tclient and not director) else None
        text(s, ended or self.my_status(st, me), 28, (W // 2, 84), ERR if ended else ACCENT, center=True)
        if st:
            colw = (W - 80) // st["rounds"]
            for r in range(st["rounds"]):
                name = "Final" if r == st["rounds"] - 1 else "Semifinals" if r == st["rounds"] - 2 \
                    else "Round %d" % (r + 1)
                text(s, name, 22, (40 + r * colw + colw // 2 - 9, 122), MUTED, center=True)
            mouse = pygame.mouse.get_pos()
            boxes = self.boxes(st)
            k, adv, _ = t_layout(st["variant"], st["teams"])
            feed = k // adv                            # matches that feed one match of the next round
            sizes = t_round_sizes(st["variant"], st["teams"], st["rounds"])
            starts = [sum(sz // k for sz in sizes[:r]) for r in range(len(sizes))]
            for r in range(len(sizes) - 1):            # bracket lines
                for i in range(sizes[r] // k):
                    a_ = boxes[starts[r] + i][1]
                    b_ = boxes[starts[r + 1] + i // feed][1]
                    xm = (a_.right + b_.x) // 2
                    pygame.draw.lines(s, (78, 74, 70), False, [a_.midright, (xm, a_.centery), (xm, b_.centery),
                                                               b_.midleft], 2)
            for m, rect, rh in boxes:
                live = m and m["status"] == "live"
                hover = live and rect.collidepoint(mouse) and not (a.parked and not a.parked.result)
                pygame.draw.rect(s, (44, 42, 39) if hover else (28, 26, 24), rect, border_radius=6)
                pygame.draw.rect(s, ACCENT if live else (68, 64, 60), rect, 2, border_radius=6)
                if not m:
                    text(s, "TBD", max(14, rh), (rect.x + 8, rect.y + 4), (100, 96, 90))
                    continue
                for j, slot in enumerate(m["slots"]):
                    nm = st["names"][slot][:18]
                    won = slot in m["winners"]
                    col = ACCENT if won else (MUTED if m["status"] == "done" else TEXT)
                    if slot == me:
                        nm = "> " + nm
                    text(s, nm, max(14, rh), (rect.x + 8, rect.y + 4 + j * rh), col)
                if st["teams"] and len(m["slots"]) == 4:      # pairs are teams
                    yy = rect.y + 4 + 2 * rh - 1
                    pygame.draw.line(s, (68, 64, 60), (rect.x + 6, yy), (rect.right - 6, yy), 1)
                note = m["note"] if m["status"] == "done" else ("LIVE - click to watch" if hover else "")
                if note:
                    text(s, note[:int(rect.w / 6.5)], max(12, rh - 3), (rect.x + 8, rect.y + 5 + len(m["slots"]) * rh),
                         ACCENT if live else MUTED)
                if live:
                    text(s, "LIVE", max(13, rh - 2), (rect.right - 6, rect.y + 4), ACCENT, right=True)
        button(s, self.BACK, "Menu")
        if a.parked:
            button(s, self.RETURN, "Return to my match", selected=not a.parked.result)
        button(s, self.END, ("End tournament" if director else "Leave tournament") if not
               (st and st.get("champions")) else "Close tournament")


# ----------------------------------------------------------------------------
# App / menu
# ----------------------------------------------------------------------------
# Display names.  The internal keys stay as they were (they are part of the LAN protocol):
#   "military" = the 9x10 / 17x17 layout, shown as "Army";  "army" = the modern units, shown as "Military".
VARIANTS = [("normal", "Normal"), ("blitz", "Blitz"), ("military", "Army"), ("army", "Military"),
            ("fullarmy", "Full Military"), ("4p", "4 Player"), ("4pmil", "4P Army"), ("4parmy", "4P Military"),
            ("4pfull", "4P Full Military")]
ARMY_RULES = ("Soldier fires at the piece ahead, Helicopter jumps twice, Artillery fires at any piece (3-turn cooldown), "
              "Tank rolls over enemy pieces to its square, Jet blasts every enemy non-king piece next to its capture.")
DESCR = {
    "normal": "Standard chess: castling, en passant, 50-move and repetition draws. Promote to Q, R, B or N.",
    "blitz": "Standard chess with a 3 minute clock and a 2 second increment per move.",
    "military": "9x10 board. Per side: back row of rooks & queens, a row of knights & bishops, two rows of pawns.",
    "army": "Standard rules with modern military units. " + ARMY_RULES,
    "fullarmy": "Army layout (9x10) with the Military units: lots of tanks, artillery and helicopters. " + ARMY_RULES,
    "4p": "Free-for-all on a 14x14 cross board with castling. Red moves first, then Blue, Yellow, Green.",
    "4pmil": "4 Player on a 17x17 cross board with the Army setup (4 rows per side). No castling.",
    "4parmy": "4 Player free-for-all with the Military units. " + ARMY_RULES,
    "4pfull": "4 Player on the 17x17 Army layout with the Military units. " + ARMY_RULES,
}
TEAMS_NOTE = " TEAMS 2v2: Red + Yellow vs Blue + Green. Allies never capture, shoot or blast each other."


def is4(v):
    return v.startswith("4p")


class App:
    def __init__(self):
        pygame.init()
        pygame.display.set_caption("Pygame Chess")
        self.screen = pygame.display.set_mode((W, H), pygame.SCALED | pygame.RESIZABLE)
        self.clock = pygame.time.Clock()
        self.glyphs = Glyphs()
        self.state = "menu"
        self.variant, self.elo, self.side = "normal", 900, "white"
        self.side4 = "red"                 # 4 Player color: "red" or "random"
        self.teams = False
        self.game = None
        self.lobby = Lobby(self)
        self.inbox = Inbox(self)
        self.td = None                     # tournament we organize
        self.tclient = None                # tournament we joined
        self.tview = TournamentView(self)
        self.parked = None                 # your live tournament match while you look at the bracket
        self.inbox.open()                  # challenges can arrive at any time
        pygame.key.set_repeat(400, 35)     # hold a key to repeat it (text boxes)

    # fullscreen (F11 or F; the window is scaled to fit, so the layout never changes)
    def is_fullscreen(self):
        surf = pygame.display.get_surface()
        return bool(surf and surf.get_flags() & pygame.FULLSCREEN)

    def toggle_fullscreen(self):
        try:
            pygame.display.toggle_fullscreen()
        except Exception as exc:
            print("fullscreen unavailable:", exc)

    def start(self):
        v = self.variant
        if is4(v):
            seat = random.randrange(4) if self.side4 == "random" else 0
            self.game = Game4P(self.glyphs, self.elo, "military" if v in ("4pmil", "4pfull") else "standard",
                               v in ("4parmy", "4pfull"), self.teams, seat)
        else:
            side = {"white": 1, "black": -1, "random": random.choice((1, -1))}[self.side]
            self.game = Game2P(self.glyphs, v, self.elo, side)
        self.state = "game"

    FS_RECT = pygame.Rect(W - 230, 16, 210, 40)
    LAN_RECT = pygame.Rect(80 + 3 * 210, 468, 190, 46)
    INBOX_RECT = pygame.Rect(80 + 3 * 210, 672, 190, 46)

    def open_lobby(self):
        self.inbox.open()
        self.state = "lan"

    TOURN_RECT = pygame.Rect(80, 672, 190, 46)

    def open_tournament(self):
        if self.tclient:
            self.state = "tournament"
        else:
            if self.td is None:
                self.td = TournamentDirector(self)
            self.state = "tsetup" if self.td.phase in ("setup", "inviting") else "tournament"

    def switch_game(self, game):
        """Replace whatever is on screen with a new game (tournament matches / spectating)."""
        if self.state == "game" and self.game is not None and self.game is not game:
            old = self.game
            old.dead = True
            if hasattr(old, "close"):
                old.close()
        self.drop_parked()
        self.begin_net_game(game)

    def drop_parked(self):
        if self.parked:
            self.parked.dead = True
            self.parked.close()
            self.parked = None

    def return_to_match(self):
        if self.parked:
            self.game, self.parked = self.parked, None
            self.state = "game"

    def begin_net_game(self, game):
        if self.game:
            self.game.dead = True
        self.game = game
        self.state = "game"

    def leave_game(self):
        """Back out of the current game: LAN games hang up and return to the LAN / Challenges screen.
        A tournament match that is still being played is only set aside: it keeps running and you can return."""
        g = self.game
        if getattr(g, "tournament", False) and not g.result:
            self.parked, self.game = g, None
            self.state = "tournament"
            return
        self.game.dead = True
        if isinstance(self.game, (NetGame2P, NetGame4P, SpecGame2P, SpecGame4P)):
            self.game.close()
            self.state = self.game.back_to
            self.lobby.say("")
        else:
            self.state = "menu"

    def menu_layout(self):
        items = []
        for n, (key, label) in enumerate(VARIANTS):
            items.append(("variant", key, label, pygame.Rect(80 + (n % 4) * 210, 112 + (n // 4) * 55, 190, 48)))
        n = len(VARIANTS)
        items.append(("teams", True, "Teams 2v2", pygame.Rect(80 + (n % 4) * 210, 112 + (n // 4) * 55, 190, 48)))
        for n, e in enumerate(ELOS):
            items.append(("elo", e, str(e), pygame.Rect(80 + (n % 4) * 210, 318 + (n // 4) * 56, 190, 46)))
        if is4(self.variant):
            for n, (key, label) in enumerate((("red", "Red"), ("random", "Random color"))):
                items.append(("side4", key, label, pygame.Rect(80 + n * 210, 468, 190, 46)))
        else:
            for n, (key, label) in enumerate((("white", "White"), ("black", "Black"), ("random", "Random"))):
                items.append(("side", key, label, pygame.Rect(80 + n * 210, 468, 190, 46)))
        return items

    def draw_menu(self):
        s = self.screen
        s.fill(BG)
        text(s, "PYGAME CHESS", 72, (W // 2, 60), TEXT, center=True)
        button(s, self.FS_RECT, "Fullscreen (F11)", self.is_fullscreen())
        text(s, "Variant", 28, (80, 84), MUTED)
        text(s, "Bot strength (Elo, approximate)", 28, (80, 288), MUTED)
        if is4(self.variant):
            ally = ("  (ally: Yellow)" if self.side4 == "red" else "  (your ally sits opposite you)") \
                if self.teams else ""
            text(s, "Your color" + ally, 28, (80, 440), MUTED)
        else:
            text(s, "Your side", 28, (80, 440), MUTED)
        for kind, val, label, rect in self.menu_layout():
            sel = (kind == "variant" and val == self.variant) or (kind == "elo" and val == self.elo) \
                or (kind == "side" and val == self.side) or (kind == "side4" and val == self.side4) \
                or (kind == "teams" and self.teams and is4(self.variant))
            off = kind == "teams" and not is4(self.variant)
            button(s, rect, label, sel, enabled=not off)
        y = 534
        descr = DESCR[self.variant] + (TEAMS_NOTE if (self.teams and is4(self.variant)) else "")
        for line in textwrap.wrap(descr, 100)[:4]:
            text(s, line, 23, (W // 2, y), TEXT, center=True)
            y += 25
        text(s, "Low Elo = random blunders; higher Elo searches deeper (depth 1 -> 5).", 22,
             (W // 2, 640), MUTED, center=True)
        button(s, pygame.Rect(W // 2 - 110, 665, 220, 60), "START GAME")
        button(s, self.LAN_RECT, "LAN Play")
        live = self.tclient or (self.td and self.td.phase != "setup")
        button(s, self.TOURN_RECT, "Tournament (live)" if live else "Tournament", bool(live))
        self.inbox.draw_button(s, self.INBOX_RECT)

    def menu_click(self, pos):
        if self.FS_RECT.collidepoint(pos):
            self.toggle_fullscreen()
            return
        if self.LAN_RECT.collidepoint(pos):
            self.open_lobby()
            return
        if self.INBOX_RECT.collidepoint(pos):
            self.state = "challenges"
            return
        if self.TOURN_RECT.collidepoint(pos):
            self.open_tournament()
            return
        for kind, val, label, rect in self.menu_layout():
            if rect.collidepoint(pos):
                if kind == "teams":
                    if is4(self.variant):
                        self.teams = not self.teams
                elif kind == "variant":
                    self.variant = val
                elif kind == "elo":
                    self.elo = val
                elif kind == "side":
                    self.side = val
                elif kind == "side4":
                    self.side4 = val
        if pygame.Rect(W // 2 - 110, 665, 220, 60).collidepoint(pos):
            self.start()

    def game_click(self, pos):
        if hasattr(self.game, "chat_click") and self.game.chat_click(pos):
            return
        for label, rect in self.game.buttons():
            if rect.collidepoint(pos):
                self.game.press(label)
                if label == "Menu":
                    self.leave_game()
                elif label == "Restart":
                    self.game.dead = True
                    self.start()
                return
        self.game.click(pos)

    def run(self):
        while True:
            for e in pygame.event.get():
                if e.type == pygame.QUIT:
                    pygame.quit()
                    sys.exit()
                if e.type == pygame.KEYDOWN and self.state == "game" and hasattr(self.game, "chat_key") \
                        and self.game.chat_key(e):
                    continue
                if e.type == pygame.KEYDOWN:
                    if e.key == pygame.K_F11 or (e.key == pygame.K_f and self.state == "game"):
                        self.toggle_fullscreen()
                    elif e.key == pygame.K_ESCAPE:
                        if self.is_fullscreen():
                            self.toggle_fullscreen()
                        elif self.state == "game":
                            self.leave_game()
                        elif self.state == "lan":
                            self.lobby.cancel("")
                            self.lobby.stop_watch()
                            self.state = "menu"
                        elif self.state in ("challenges", "tournament", "tsetup"):
                            self.state = "menu"
                    elif self.state == "lan":
                        self.lobby.key(e)
                    elif self.state == "tsetup":
                        self.td.key(e)
                if e.type == pygame.MOUSEBUTTONDOWN:
                    if e.button == 1:
                        if self.state == "game":
                            self.game.plan_clear()          # a left click wipes the planning arrows / marks
                        {"menu": self.menu_click, "lan": self.lobby.click, "challenges": self.inbox.click,
                         "game": self.game_click, "tournament": self.tview.click,
                         "tsetup": lambda pos: self.td.click(pos)}[self.state](e.pos)
                    elif e.button == 3 and self.state == "game":
                        self.game.cancel()
                        self.game.plan_down(e.pos)
                if e.type == pygame.MOUSEBUTTONUP and e.button == 3 and self.state == "game":
                    self.game.plan_up(e.pos)
            self.lobby.pump()
            self.inbox.pump()
            if self.td:
                self.td.pump()
            if self.tclient:
                self.tclient.pump()
            if self.parked:                         # a set-aside tournament match keeps running
                self.parked.update()
                if getattr(self.parked, "next_game", None):
                    old, self.parked = self.parked, self.parked.next_game
                    self.parked.adopt_spectators(old)
            if self.state == "menu":
                self.draw_menu()
            elif self.state == "lan":
                self.lobby.draw(self.screen)
            elif self.state == "challenges":
                self.inbox.draw(self.screen)
            elif self.state == "tsetup":
                self.td.draw(self.screen)
            elif self.state == "tournament":
                self.tview.draw(self.screen)
            else:
                self.game.update()
                if getattr(self.game, "next_game", None):       # LAN rematch / re-sync: swap in the new game
                    old, self.game = self.game, self.game.next_game
                    if hasattr(self.game, "adopt_spectators"):
                        self.game.adopt_spectators(old)
                self.screen.fill(BG)
                self.game.draw(self.screen)
                text(self.screen, "Enter = chat    F = fullscreen" if hasattr(self.game, "chat_key")
                     else "F = fullscreen", 18, (W - 12, 742), MUTED, right=True)
            if self.state != "challenges":
                self.inbox.draw_toast(self.screen)
            pygame.display.flip()
            self.clock.tick(60)


if __name__ == "__main__":
    App().run()