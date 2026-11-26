#!/usr/bin/env python3
"""
Pygame Chess launcher
---------------------
Checks the latest chess.py on GitHub (adventure-car/pygame-chess), updates your local copy if it changed,
then starts the game.  It also keeps itself up to date (chess_launcher.py in the same repo).
Uses only the Python standard library.

    python3 chess_launcher.py                         # opens the launcher window
    python3 chess_launcher.py --path C:/Games/chess.py --cli    # no window: update, then play
    python3 chess_launcher.py --path ~/chess.py --cli --no-launch   # just update

The chess.py path you choose is remembered in launcher_settings.json next to this file.
A copy of your previous chess.py is kept as chess.py.bak whenever an update is installed.
"""
import argparse
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import tempfile
import threading
import time
import urllib.error
import urllib.request

LAUNCHER_VERSION = 2       # bump this whenever chess_launcher.py changes, so copies only ever move forward
REPO = "adventure-car/pygame-chess"
BRANCH = "main"
RAW_URL = "https://raw.githubusercontent.com/%s/%s/chess.py" % (REPO, BRANCH)
LAUNCHER_URL = "https://raw.githubusercontent.com/%s/%s/chess_launcher.py" % (REPO, BRANCH)
LAUNCHER_MARKER = b"Pygame Chess launcher"   # a real launcher always contains this
SELF = os.path.abspath(__file__)
SETTINGS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "launcher_settings.json")
MIN_SIZE = 10_000          # anything smaller than this can't be the real game (e.g. an error page)


# ----------------------------------------------------------------------------
# Settings
# ----------------------------------------------------------------------------
def load_path():
    try:
        with open(SETTINGS, encoding="utf-8") as f:
            return json.load(f).get("chess_path", "")
    except (OSError, ValueError):
        return ""


def save_path(path):
    try:
        with open(SETTINGS, "w", encoding="utf-8") as f:
            json.dump({"chess_path": path}, f, indent=2)
    except OSError:
        pass


def normalize(path):
    """Accept a file path or a folder (then chess.py inside it is used)."""
    path = os.path.abspath(os.path.expanduser(path.strip().strip('"')))
    if os.path.isdir(path) or not path.lower().endswith(".py"):     # a folder (new or existing)
        path = os.path.join(path, "chess.py")
    return path


# ----------------------------------------------------------------------------
# Update logic
# ----------------------------------------------------------------------------
class NotOnGitHub(RuntimeError):
    pass


def download_latest(url=RAW_URL, min_size=MIN_SIZE, name="chess.py", timeout=15):
    """Fetch the newest copy of a file from GitHub.  Raises an exception with a readable message on failure."""
    url = "%s?nocache=%d" % (url, int(time.time()))              # dodge stale CDN copies
    req = urllib.request.Request(url, headers={"User-Agent": "pygame-chess-launcher",
                                               "Cache-Control": "no-cache"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            data = r.read()
    except urllib.error.HTTPError as exc:
        if exc.code == 404:
            raise NotOnGitHub("%s isn't on GitHub" % name)
        raise RuntimeError("GitHub answered %d %s" % (exc.code, exc.reason))
    except (urllib.error.URLError, OSError) as exc:
        raise RuntimeError("no connection to GitHub (%s)" % getattr(exc, "reason", exc))
    if len(data) < min_size:
        raise RuntimeError("the downloaded %s is too small to be real" % name)
    try:
        compile(data, name, "exec")                                  # never install a broken file
    except SyntaxError as exc:
        raise RuntimeError("the downloaded file has a syntax error (line %s)" % exc.lineno)
    return data


def sha(data):
    return hashlib.sha256(data).hexdigest()


def same_text(a, b):
    """Equal apart from Windows/Unix line endings."""
    return sha(a.replace(b"\r\n", b"\n")) == sha(b.replace(b"\r\n", b"\n"))


def write_atomic(path, data, backup):
    folder = os.path.dirname(path) or "."
    os.makedirs(folder, exist_ok=True)
    if backup is not None:
        with open(path + ".bak", "wb") as f:
            f.write(backup)
    fd, tmp = tempfile.mkstemp(dir=folder, prefix=".upd_", suffix=".tmp")
    with os.fdopen(fd, "wb") as f:
        f.write(data)
    os.replace(tmp, path)                      # atomic: the old file stays intact if anything fails


def self_update(log=print):
    """Replace this launcher with the newest one on GitHub.  Returns True if it was replaced."""
    try:
        new = download_latest(LAUNCHER_URL, 2000, "chess_launcher.py", timeout=8)
    except NotOnGitHub:
        return False                           # the repo doesn't ship a launcher (yet): nothing to do
    except RuntimeError as exc:
        log("Couldn't check for a launcher update: %s." % exc)
        return False
    if LAUNCHER_MARKER not in new:
        log("Ignored a launcher update that doesn't look like this launcher.")
        return False
    found = re.search(rb"^LAUNCHER_VERSION\s*=\s*(\d+)", new, re.M)
    if not found or int(found.group(1)) <= LAUNCHER_VERSION:
        return False                           # same or older than this one: never downgrade
    with open(SELF, "rb") as f:
        mine = f.read()
    try:
        write_atomic(SELF, new, mine)
    except OSError as exc:
        log("Couldn't update the launcher: %s" % (exc.strerror or exc))
        return False
    log("The launcher updated itself (old copy saved as %s.bak)" % os.path.basename(SELF) + ". Restarting it...")
    return True


def restart_self(argv):
    """Run the freshly updated launcher with the same options (and never self-update twice in a row)."""
    cmd = [sys.executable, SELF] + [a for a in argv if a != "--no-self-update"] + ["--no-self-update",
                                                                                 "--launcher-updated"]
    if os.name == "nt":
        sys.exit(subprocess.call(cmd))
    os.execv(sys.executable, cmd)


def update(path, log=print):
    """Bring the chess.py at `path` up to date.  Returns True if the game file is ready to run."""
    have = None
    if os.path.isfile(path):
        with open(path, "rb") as f:
            have = f.read()
    log("Checking GitHub for the latest version...")
    try:
        new = download_latest()
    except RuntimeError as exc:
        if have is not None:
            log("Couldn't check for updates: %s. Using your current copy." % exc)
            return True
        log("Couldn't download the game: %s." % exc)
        return False
    # Line endings can differ on Windows (git autocrlf) - don't count that as a change.
    if have is not None and same_text(have, new):
        log("You already have the latest version.")
        return True
    try:
        write_atomic(path, new, have)
    except OSError as exc:
        log("Couldn't write %s: %s" % (path, exc.strerror or exc))
        return have is not None
    log(("Updated to the latest version (old copy saved as %s.bak)." % os.path.basename(path))
        if have is not None else "Downloaded the game to %s." % path)
    return True


# ----------------------------------------------------------------------------
# Launching
# ----------------------------------------------------------------------------
def pygame_installed():
    return importlib.util.find_spec("pygame") is not None


def install_pygame(log=print):
    log("Installing pygame-ce (this can take a minute)...")
    r = subprocess.run([sys.executable, "-m", "pip", "install", "--user", "pygame-ce"],
                       capture_output=True, text=True)
    if r.returncode != 0:
        r = subprocess.run([sys.executable, "-m", "pip", "install", "pygame-ce"], capture_output=True, text=True)
    importlib.invalidate_caches()
    ok = r.returncode == 0
    log("pygame-ce installed." if ok else "Couldn't install pygame-ce:\n" + (r.stderr or r.stdout)[-400:])
    return ok


def launch(path):
    """Start the game as its own process, in its own folder."""
    folder = os.path.dirname(path)
    kwargs = {}
    if os.name == "nt":
        kwargs["creationflags"] = 0x00000008          # DETACHED_PROCESS: keep running if the launcher closes
    else:
        kwargs["start_new_session"] = True
    return subprocess.Popen([sys.executable, path], cwd=folder, **kwargs)


# ----------------------------------------------------------------------------
# Command line
# ----------------------------------------------------------------------------
def run_cli(path, no_launch):
    if not path:
        path = input("Path to chess.py (or the folder to put it in): ")
    path = normalize(path)
    save_path(path)
    if not update(path):
        return 1
    if no_launch:
        return 0
    if not pygame_installed():
        if input("pygame-ce isn't installed. Install it now? [Y/n] ").strip().lower() in ("", "y", "yes"):
            if not install_pygame():
                return 1
        else:
            return 1
    print("Starting the game...")
    return subprocess.call([sys.executable, path], cwd=os.path.dirname(path))


# ----------------------------------------------------------------------------
# Window
# ----------------------------------------------------------------------------
def run_gui(initial, notes=()):
    import tkinter as tk
    from tkinter import filedialog, messagebox

    root = tk.Tk()
    root.title("Pygame Chess Launcher")
    root.resizable(False, False)
    pad = {"padx": 10, "pady": 6}

    tk.Label(root, text="PYGAME CHESS", font=("Helvetica", 20, "bold")).grid(row=0, column=0, columnspan=3, **pad)
    tk.Label(root, text="Your chess.py:").grid(row=1, column=0, sticky="w", **pad)
    path_var = tk.StringVar(value=initial)
    entry = tk.Entry(root, textvariable=path_var, width=52)
    entry.grid(row=1, column=1, **pad)

    def browse():
        start = os.path.dirname(path_var.get()) or os.path.expanduser("~")
        p = filedialog.asksaveasfilename(title="Where is (or where should I put) chess.py?", initialdir=start,
                                         initialfile="chess.py", defaultextension=".py",
                                         filetypes=[("Python file", "*.py")], confirmoverwrite=False)
        if p:
            path_var.set(p)

    tk.Button(root, text="Browse...", command=browse).grid(row=1, column=2, **pad)
    status = tk.Text(root, height=7, width=72, state="disabled", wrap="word", relief="groove")
    status.grid(row=3, column=0, columnspan=3, **pad)

    def log(msg):                                     # safe to call from the worker thread
        def put():
            status.configure(state="normal")
            status.insert("end", msg + "\n")
            status.see("end")
            status.configure(state="disabled")
        root.after(0, put)

    buttons = []

    def busy(on):
        root.after(0, lambda: [b.configure(state="disabled" if on else "normal") for b in buttons])

    def work(play):
        try:
            path = normalize(path_var.get())
            root.after(0, lambda: path_var.set(path))
            save_path(path)
            if not update(path, log) or not play:
                return
            if not pygame_installed():
                ask = []
                ev = threading.Event()

                def question():
                    ask.append(messagebox.askyesno("pygame-ce missing",
                                                   "The game needs pygame-ce, which isn't installed.\nInstall it now?"))
                    ev.set()
                root.after(0, question)
                ev.wait()
                if not ask[0] or not install_pygame(log):
                    return
            log("Starting the game...")
            launch(path)
            root.after(800, root.destroy)
        except Exception as exc:                      # keep the window usable whatever happens
            log("Something went wrong: %s" % exc)
        finally:
            busy(False)

    def start(play):
        if not path_var.get().strip():
            messagebox.showinfo("Choose a location", "Pick where your chess.py is (or should go) first.")
            return
        busy(True)
        threading.Thread(target=work, args=(play,), daemon=True).start()

    row = tk.Frame(root)
    row.grid(row=2, column=0, columnspan=3, **pad)
    buttons.append(tk.Button(row, text="Update & Play", width=18, command=lambda: start(True)))
    buttons.append(tk.Button(row, text="Check for updates only", width=22, command=lambda: start(False)))
    for b in buttons:
        b.pack(side="left", padx=8)
    log("Source: github.com/%s (%s branch)" % (REPO, BRANCH))
    for n in notes:
        log(n)
    entry.focus_set()
    root.bind("<Return>", lambda e: start(True))
    root.mainloop()


def main():
    ap = argparse.ArgumentParser(description="Update chess.py from GitHub, then start the game.")
    ap.add_argument("--path", help="your chess.py (or the folder to put it in); remembered for next time")
    ap.add_argument("--cli", action="store_true", help="no window, use the terminal")
    ap.add_argument("--no-launch", action="store_true", help="only update, don't start the game")
    ap.add_argument("--no-self-update", action="store_true", help="don't check for a newer launcher")
    ap.add_argument("--launcher-updated", action="store_true", help=argparse.SUPPRESS)
    args = ap.parse_args()
    if not args.no_self_update and self_update():
        restart_self(sys.argv[1:])
    notes = ["The launcher updated itself to the latest version."] if args.launcher_updated else []
    path = args.path or load_path()
    if not args.cli:
        try:
            run_gui(normalize(path) if path else "", notes)
            return 0
        except Exception as exc:                      # no tkinter / no display: fall back to the terminal
            print("(No launcher window available: %s - using the terminal.)" % exc)
    for n in notes:
        print(n)
    return run_cli(path, args.no_launch)


if __name__ == "__main__":
    sys.exit(main())
