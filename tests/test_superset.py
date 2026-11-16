#!/usr/bin/env python3
"""Superset check: every position of a real or random game must be a candidate.

Positions come from the reference engine (chushogi/, lishogi rules): the 49
lishogi game records shipped with it, plus random self-play.  Each board must
pass is_candidate at the tightest level (file-exact + I6/I7), and the side that
has just moved must own a royal.  This tests necessity of the invariants in
docs/invariants.md empirically; it cannot show that they are complete.

Usage: python3 tests/test_superset.py [--games N] [--seed S] [--engine PATH]
The engine is built with `make engine` (default path out/engine/chushogi-gen).
"""
import argparse
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))
from count import sfen as sfenlib                                   # noqa: E402
from count.candidates import Royal, chu_setup, is_candidate         # noqa: E402
from plan.lanes import lane_ok                                      # noqa: E402


class Engine:
    def __init__(self, path):
        self.p = subprocess.Popen([path], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)

    def ask(self, cmd):
        self.p.stdin.write(cmd + "\n")
        self.p.stdin.flush()
        return self.p.stdout.readline().strip()


def check(sfen, setup, stats):
    board, turn, _ = sfenlib.parse(sfen)
    assert is_candidate(setup, board, "file", colour=True), sfen
    assert lane_ok(board), ("I10", sfen)
    mover_done = "W" if turn == "B" else "B"
    assert any(c == mover_done and role in ("K", "+E") for c, role in board.values()), sfen
    stats["positions"] += 1
    stats["promoted"] += sum(role.startswith("+") for _, role in board.values())
    stats["min_pieces"] = min(stats["min_pieces"], len(board))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--games", type=int, default=100)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--engine", default=os.environ.get("CHU_ENGINE", str(ROOT / "out" / "engine" / "chushogi-gen")))
    args = ap.parse_args()
    if not Path(args.engine).exists():
        sys.exit(f"engine not found at {args.engine}; build it with `make engine`")
    setup = chu_setup(identify_royals=True)
    for c in "BW":                      # royals are checked separately, per side to move
        setup.free[c][0] = Royal(required=False, identify=True)
    eng = Engine(args.engine)
    stats = {"positions": 0, "promoted": 0, "min_pieces": 92}

    cases = ROOT / "out" / "engine" / "tests" / "chushogi_cases.tsv"
    skipped = 0
    for line in cases.open():
        cmd = line.split("\t")[0]
        if not cmd.startswith(f"position sfen {sfenlib.INITIAL}"):
            skipped += 1                # a record that starts from a composed position
            continue
        assert eng.ask(cmd) == "ok"
        check(eng.ask("sfen")[5:], setup, stats)
    print(f"game records: {stats} ({skipped} positions not from the initial array skipped)")

    eng.ask(f"seed {args.seed}")
    ended = {}
    for g in range(args.games):
        assert eng.ask(f"position sfen {sfenlib.INITIAL}") == "ok"
        for ply in range(2000):
            status = eng.ask("status").split()[1]
            if status != "playing":
                break
            move = eng.ask("go random").split()[1]
            assert eng.ask(f"move {move}") == "ok"
            check(eng.ask("sfen")[5:], setup, stats)
        ended[status] = ended.get(status, 0) + 1
    print(f"+ {args.games} random games (seed {args.seed}): {stats}; endings {ended}")
    print("ok")


if __name__ == "__main__":
    main()
