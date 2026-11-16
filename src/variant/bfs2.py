#!/usr/bin/env python3
"""Exhaustive search of a validation variant with the candidate set's ranking
as a perfect hash: one bit per candidate board for Black-to-move states, one
bit per candidate board for White-to-move states (through the 180-degree
colour swap, which maps them into the same candidate set), and per-flag-square
bitsets for flagged states.  A reachable state whose board fails to rank is a
superset violation (C does not contain R) and is reported.

Usage: python3 src/variant/bfs2.py V1 [--limit N]
"""
import argparse
import sys
import time
from collections import Counter, deque
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.candidates import count                                   # noqa: E402
from count.sampler import Ranker, Sampler                             # noqa: E402
from plan.lanes import Geometry, lane_ok                               # noqa: E402
from variant.bfs import variants                                     # noqa: E402


class Bits:
    def __init__(self, n):
        self.a = bytearray((n + 7) // 8)
        self.count = 0

    def test_and_set(self, i):
        b, m = i >> 3, 1 << (i & 7)
        if self.a[b] & m:
            return True
        self.a[b] |= m
        self.count += 1
        return False


def run(name, limit=None):
    var, setup, colour = variants()[name]
    t0 = time.time()
    sampler = Sampler(setup, "file", colour)
    ranker = Ranker(sampler)
    total = sampler.total
    assert total == count(setup, "file", colour).total
    nf, nr = setup.nfiles, setup.nranks

    def rotate(bd):
        return {(nf - 1 - x, nr + 1 - r): ("W" if c == "B" else "B", role) for (x, r), (c, role) in bd.items()}

    def rank_state(st):
        board, turn, flag = st
        bd = var.to_board_dict(board)
        if turn == "W":
            bd = rotate(bd)
        return ranker.rank(bd)

    seen = {"B": Bits(total), "W": Bits(total)}
    seen_flag = {}
    geo = Geometry(setup)
    i10_violations = []
    stats = Counter()
    violations = []

    def visit(st):
        """True if new."""
        board, turn, flag = st
        bd = var.to_board_dict(board)
        if turn == "W":
            bd = rotate(bd)
        try:
            r = ranker.rank(bd)
        except Exception as e:                              # not a candidate: superset violation
            violations.append((var.to_board_dict(board), turn, flag, repr(e)[:60]))
            return False
        if flag is None:
            new = not seen[turn].test_and_set(r)
            if new and not lane_ok(bd, geo):
                i10_violations.append((bd, turn))
            return new
        key = (turn, flag)
        if key not in seen_flag:
            seen_flag[key] = Bits(total)
        return not seen_flag[key].test_and_set(r)

    q = deque([var.start])
    visit(var.start)
    n = 1
    last = 0
    while q:
        st = q.popleft()
        status = var.status(st)
        board, turn, flag = st
        if turn == "B":
            stats[("B", status != "playing")] += 1
            if flag is None:
                stats["flag-none"] += 1
            else:
                with_flag, no_flag = set(var.legal_moves(st)), set(var.legal_moves((board, turn, None)))
                stats["flag-effective" if with_flag != no_flag else "flag-ineffective"] += 1
            stats[status] += 1
        else:
            stats[("W", status != "playing")] += 1
        if status != "playing":
            continue
        for mv in var.legal_moves(st):
            nxt = var.apply(st, mv)
            if visit(nxt):
                q.append(nxt)
                n += 1
                if limit and n >= limit:
                    q.clear()
                    break
        if n - last >= 500000:
            last = n
            print(f"  ... {n} states, queue {len(q)}, {time.time() - t0:.0f}s", flush=True)
    boards_b = seen["B"].count
    print(f"{name}: {n} reachable states in {time.time() - t0:.0f}s" + ("  (LIMIT HIT)" if limit and n >= limit else ""))
    print(f"  Black to move: non-terminal {stats[('B', False)]}, terminal {stats[('B', True)]}"
          f" (royalslost {stats['royalslost']}, bareking {stats['bareking']}, stalemate {stats['stalemate']}, draw {stats['draw']});"
          f" White to move: {stats[('W', False)] + stats[('W', True)]}")
    print(f"  Black-to-move states by flag: none {stats['flag-none']}, effective {stats['flag-effective']}, ineffective {stats['flag-ineffective']}")
    print(f"  reachable Black-to-move boards |R| = {boards_b}; |C| = {total}; |R|/|C| = {boards_b / total:.5f}")
    print(f"  superset violations (states that fail to rank): {len(violations)}; I10 violations: {len(i10_violations)}")
    for v in violations[:5]:
        print("    ", v)
    return stats, violations


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("name")
    ap.add_argument("--limit", type=int)
    a = ap.parse_args()
    run(a.name, a.limit)
