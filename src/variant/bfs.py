#!/usr/bin/env python3
"""Exhaustive forward search of a validation variant, and comparison with its
candidate set.

Usage: python3 src/variant/bfs.py V1 [--limit N]
Reports: reachable states (all / Black to move), terminal vs non-terminal,
flag states (none / effective / ineffective), reachable Black-to-move boards,
boards outside the variant's candidate set C (must be none), and |R|/|C|.
"""
import argparse
import sys
import time
from collections import Counter, deque
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.candidates import Bound, Setup, Std, count, is_candidate   # noqa: E402
from count.filegame import Slot                                       # noqa: E402
from variant.rules import Variant                                     # noqa: E402

K = lambda: Std("K", 1, promotable=False, minimum=1)
TK = lambda: Std("K", 1, promotable=False, minimum=0)     # terminal boards admitted (D4)


def variants():
    v = {}
    # V1: 3x5, zone 1.  Black: L a1, N b1, K c1, P b2.  White: rotated 180 degrees.
    start = {(0, 1): ("B", "L"), (1, 1): ("B", "N"), (2, 1): ("B", "K"), (1, 2): ("B", "P"),
             (2, 5): ("W", "L"), (1, 5): ("W", "N"), (0, 5): ("W", "K"), (1, 4): ("W", "P")}
    files = [[Slot("BL", "B", "L", 1)], [Slot("BP", "B", "P", 2), Slot("WP", "W", "P", 4)], [Slot("WL", "W", "L", 5)]]
    free = {"B": [TK(), Std("N", 1, promotable=False)], "W": [K(), Std("N", 1, promotable=False)]}
    v["V1"] = (Variant(3, 5, 1, start, ["K", "N", "P", "L", "+P", "+L"]), Setup(3, 5, 1, files, free), False)
    # V8: pawn + go-between + lion + king.  Black: GB a2, N b1, K c1, P b2.
    start = {(0, 2): ("B", "GB"), (1, 1): ("B", "N"), (2, 1): ("B", "K"), (1, 2): ("B", "P"),
             (2, 4): ("W", "GB"), (1, 5): ("W", "N"), (0, 5): ("W", "K"), (1, 4): ("W", "P")}
    files = [[Slot("BGB", "B", "GB", 2)], [Slot("BP", "B", "P", 2), Slot("WP", "W", "P", 4)], [Slot("WGB", "W", "GB", 4)]]
    v["V8"] = (Variant(3, 5, 1, start, ["K", "N", "P", "GB", "+P", "+GB"]), Setup(3, 5, 1, files, free), False)
    # V6: lance + pawn + one colour-bound bishop + king (no lion).  Black: L a1, B b1, K c1, P b2.
    start = {(0, 1): ("B", "L"), (1, 1): ("B", "B"), (2, 1): ("B", "K"), (1, 2): ("B", "P"),
             (2, 5): ("W", "L"), (1, 5): ("W", "B"), (0, 5): ("W", "K"), (1, 4): ("W", "P")}
    files = [[Slot("BL", "B", "L", 1)], [Slot("BP", "B", "P", 2), Slot("WP", "W", "P", 4)], [Slot("WL", "W", "L", 5)]]
    free = {"B": [TK(), Bound("B", (0,))], "W": [K(), Bound("B", (0,))]}
    v["V6"] = (Variant(3, 5, 1, start, ["K", "B", "P", "L", "+P", "+L", "+B"]), Setup(3, 5, 1, files, free), True)
    return v


def run(name, limit=None):
    var, setup, colour = variants()[name]
    t0 = time.time()

    def pack(st):
        board, turn, flag = st
        v = 0
        for c in board:
            v = v * 16 + c
        return (v * 2 + (turn == "W")) * 32 + (31 if flag is None else flag)

    def unpack(v):
        v, f = divmod(v, 32)
        v, t = divmod(v, 2)
        board = []
        for _ in range(var.n):
            v, c = divmod(v, 16)
            board.append(c)
        return tuple(reversed(board)), "W" if t else "B", None if f == 31 else f

    seen = {pack(var.start)}
    q = deque([pack(var.start)])
    last_report = 0
    stats = Counter()
    boards = set()
    bad = []
    while q:
        st = unpack(q.popleft())
        status = var.status(st)
        board, turn, flag = st
        if turn == "B":
            key = ("B", status != "playing")
            stats[key] += 1
            if flag is None:
                stats["flag-none"] += 1
            else:
                no_flag = set(var.legal_moves((board, turn, None)))
                with_flag = set(var.legal_moves(st))
                stats["flag-effective" if with_flag != no_flag else "flag-ineffective"] += 1
            if board not in boards:
                boards.add(board)
                bd = var.to_board_dict(board)
                if not is_candidate(setup, bd, "file", colour):
                    bad.append(bd)
        else:
            stats[("W", status != "playing")] += 1
        if status != "playing":
            continue
        for mv in var.legal_moves(st):
            nxt = pack(var.apply(st, mv))
            if nxt not in seen:
                seen.add(nxt)
                q.append(nxt)
                if limit and len(seen) >= limit:
                    q.clear()
                    break
        if len(seen) - last_report >= 1000000:
            last_report = len(seen)
            print(f"  ... {len(seen)} states, queue {len(q)}, {time.time() - t0:.0f}s", flush=True)
    c = count(setup, "file", colour).total
    print(f"{name}: {len(seen)} reachable states in {time.time() - t0:.0f}s" + ("  (LIMIT HIT)" if limit and len(seen) >= limit else ""))
    print(f"  Black to move: non-terminal {stats[('B', False)]}, terminal {stats[('B', True)]};"
          f" White to move: {stats[('W', False)] + stats[('W', True)]}")
    print(f"  Black-to-move states by flag: none {stats['flag-none']}, effective {stats['flag-effective']},"
          f" ineffective {stats['flag-ineffective']}")
    print(f"  reachable Black-to-move boards |R| = {len(boards)}; candidate boards |C| = {c}; |R|/|C| = {len(boards) / c:.5f}")
    print(f"  reachable boards outside C: {len(bad)}")
    for bd in bad[:5]:
        print("    ", sorted(bd.items()))
    return seen, boards, bad


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("name")
    ap.add_argument("--limit", type=int)
    a = ap.parse_args()
    run(a.name, a.limit)
