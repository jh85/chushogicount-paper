#!/usr/bin/env python3
"""Static shares of candidate boards on which the lishogi and JCSA game-end rules
differ (docs/jcsa-rules-en.md U6, U7, U10): per sampled non-terminal candidate board
(Black to move) the engine status (stalemate / bareking / draw / playing), whether
Black's royal is attacked, and whether Black is mated in the JCSA sense (one royal,
attacked, every legal move leaves it capturable).
Usage: python3 src/jcsa/endings_share.py --n 1000000 --seed 23 --procs 2
"""
import argparse
import math
import random
import sys
from collections import Counter
from multiprocessing import Pool
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

_S = None
_E = None


def _init():
    global _S, _E
    from count.candidates import PRIMARY, chu_setup
    from count.sampler import Sampler
    from plan.engine import Engine
    _S = Sampler(chu_setup("file", **PRIMARY), "file", True)
    _E = Engine()


def _work(args):
    from count.sampler import to_sfen
    from jcsa.reverify import mated, royal_capturable
    seed, n = args
    rng = random.Random(seed)
    c = Counter()
    for _ in range(n):
        board = _S.sample(rng)[0]
        if not any(p == ("B", "K") for p in board.values()):
            c["terminal-stratum board (skipped)"] += 1
            continue
        _E.position(to_sfen(board, "b"))
        st = _E.status()
        c["status:" + st] += 1
        if royal_capturable(_E, board, "B"):
            c["black royal attacked"] += 1
            if mated(_E, board, "B", None):
                c["black mated (JCSA R-E1)"] += 1
    return c


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=100000)
    ap.add_argument("--seed", type=int, default=23)
    ap.add_argument("--procs", type=int, default=2)
    a = ap.parse_args()
    chunks = max(a.procs * 4, a.n // 10000)
    per = a.n // chunks
    tot = Counter()
    with Pool(a.procs, initializer=_init) as pool:
        for i, c in enumerate(pool.imap_unordered(_work, [(a.seed * 1009 + i, per) for i in range(chunks)])):
            tot.update(c)
            if (i + 1) % 20 == 0:
                print(f"  ... {sum(v for k, v in tot.items() if k.startswith('status'))} non-terminal boards", flush=True)
    n = sum(v for k, v in tot.items() if k.startswith("status"))
    print(f"non-terminal candidate boards: {n} (seed {a.seed})")
    for k, v in sorted(tot.items()):
        p = v / n
        print(f"  {k}: {v}  share {p:.2e} ± {3 * math.sqrt(max(p * (1 - p), 1 / n) / n):.1e} (3σ; ≥ 3/n if zero)")


if __name__ == "__main__":
    main()
