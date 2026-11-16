"""Wrapper around the reference engine (out/engine/chushogi-gen): the planner's
only source of legality.  Illegal moves are fatal for the engine, so every move
is checked against its legal list first."""
import os
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT = os.environ.get("CHU_ENGINE", str(ROOT / "out" / "engine" / "chushogi-gen"))


class Engine:
    def __init__(self, path=DEFAULT):
        self.p = subprocess.Popen([path], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)

    def ask(self, cmd):
        self.p.stdin.write(cmd + "\n")
        self.p.stdin.flush()
        return self.p.stdout.readline().strip()

    def position(self, sfen, moves=()):
        cmd = f"position sfen {sfen}" + (" moves " + " ".join(moves) if moves else "")
        assert self.ask(cmd) == "ok", cmd

    def legal(self):
        return set(self.ask("legal").split()[1:])

    def sfen(self):
        return self.ask("sfen")[5:]

    def status(self):
        return self.ask("status").split()[1]

    def move(self, m):
        r = self.ask(f"move {m}")
        assert r == "ok", (m, r)
