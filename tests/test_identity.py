#!/usr/bin/env python3
"""Differential test for the piece-identity merges (decision D2).

For positions taken from random self-play, relabel every lion <-> promoted
kirin, free king <-> promoted phoenix, king <-> crown prince (both colours, all
occurrences), and compare with the reference engine: the legal move list, the
game status, and the position after every legal move (relabelled back).  Any
difference would mean a rule distinguishes the two roles.

Usage: python3 tests/test_identity.py [--games N] [--seed S] [--engine PATH]
"""
import argparse
import os
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tests"))
from test_superset import Engine                                    # noqa: E402
sys.path.insert(0, str(ROOT / "src"))
from count.sfen import INITIAL                                       # noqa: E402

SWAP = {"n": "+o", "+o": "n", "q": "+x", "+x": "q", "k": "+e", "+e": "k"}
MERGE = {"+o": "n", "+x": "q", "+e": "k"}


def relabel(sfen, table=SWAP):
    rows, rest = sfen.split(" ", 1)
    out, promoted = [], False
    for ch in rows:
        if ch == "+":
            promoted = True
            continue
        tok = ("+" if promoted else "") + ch.lower()
        promoted = False
        if tok in table:
            new = table[tok]
            out.append(new.upper() if ch.isupper() else new)
        else:
            out.append(("+" if tok.startswith("+") else "") + ch)
    return "".join(out) + " " + rest


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--games", type=int, default=60)
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--moves-per-position", type=int, default=3)
    ap.add_argument("--engine", default=os.environ.get("CHU_ENGINE", str(ROOT / "out" / "engine" / "chushogi-gen")))
    args = ap.parse_args()
    rng = random.Random(args.seed)
    eng = Engine(args.engine)
    eng.ask(f"seed {args.seed}")
    positions = []
    for g in range(args.games):
        eng.ask(f"position sfen {INITIAL}")
        while eng.ask("status").split()[1] == "playing":
            eng.ask("move " + eng.ask("go random").split()[1])
            positions.append(eng.ask("sfen")[5:])
    checked = swapped_pieces = 0
    for sfen in positions:
        alt = relabel(sfen)
        assert relabel(alt) == sfen
        swapped_pieces += sum(sfen.split()[0].lower().count(t) for t in ("n", "q", "k"))
        a = {}
        for name, s in (("orig", sfen), ("swap", alt)):
            assert eng.ask(f"position sfen {s}") == "ok", s
            a[name] = (sorted(eng.ask("legal").split()[1:]), eng.ask("status"))
        assert a["orig"] == a["swap"], (sfen, a)
        for m in rng.sample(a["orig"][0], min(args.moves_per_position, len(a["orig"][0]))):
            after = {}
            for name, s in (("orig", sfen), ("swap", alt)):
                eng.ask(f"position sfen {s}")
                assert eng.ask(f"move {m}") == "ok"
                after[name] = eng.ask("sfen")[5:]
            # equal as merged states (a promotion in the swapped world creates the
            # merged role under the other name)
            assert relabel(after["orig"], MERGE) == relabel(after["swap"], MERGE), (sfen, m, after)
        checked += 1
    print(f"ok: {checked} positions, {swapped_pieces} relabelled pieces, "
          f"{args.moves_per_position} moves per position; no rule distinguishes the merged roles")


if __name__ == "__main__":
    main()
