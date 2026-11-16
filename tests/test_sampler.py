#!/usr/bin/env python3
"""Tests for src/count/sampler.py.  Run: python3 tests/test_sampler.py

1. The sampler's total weight equals the counter's count (chu shogi, primary set).
2. Uniformity: on small boards, enumerate every candidate by brute force, draw
   many samples, and check the chi-square statistic against its expectation.
3. Every chu shogi sample passes is_candidate.
"""
import math
import random
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
from count.candidates import PRIMARY, Bound, Jumper, Setup, Std, chu_setup, count, is_candidate  # noqa: E402
from count.filegame import Slot                                                                   # noqa: E402
from count.sampler import Ranker, Sampler, to_sfen                                                # noqa: E402
from count.sfen import parse                                                                      # noqa: E402


def enumerate_boards(setup, inventory, level, colour):
    squares = [(x, r) for x in range(setup.nfiles) for r in range(1, setup.nranks + 1)]
    left = [m for _, m in inventory]
    board, found = {}, []

    def rec(i):
        if i == len(squares):
            if is_candidate(setup, board, level, colour):
                found.append(frozenset(board.items()))
            return
        rec(i + 1)
        for k, (piece, _) in enumerate(inventory):
            if left[k]:
                left[k] -= 1
                board[squares[i]] = piece
                rec(i + 1)
                del board[squares[i]]
                left[k] += 1
    rec(0)
    return found


def _uniformity(setup, inventory, level, colour, per_board=40, seed=5):
    boards = enumerate_boards(setup, inventory, level, colour)
    s = Sampler(setup, level, colour)
    assert s.total == len(boards) == count(setup, level, colour).total
    # ranking is a bijection onto range(total)
    ranks = sorted(Ranker(s).rank(dict(b)) for b in boards)
    assert ranks == list(range(len(boards)))
    rng = random.Random(seed)
    n = per_board * len(boards)
    freq = Counter(frozenset(s.sample(rng)[0].items()) for _ in range(n))
    assert set(freq) <= set(boards)
    chi2 = sum((freq.get(b, 0) - per_board) ** 2 / per_board for b in boards)
    df = len(boards) - 1
    z = (chi2 - df) / math.sqrt(2 * df)
    assert abs(z) < 4, (len(boards), chi2, df, z)
    return len(boards), z


def test_uniform_pawn_files():
    f = [Slot("BP", "B", "P", 1), Slot("WP", "W", "P", 3)]
    setup = Setup(2, 3, 1, [f, f], {"B": [Std("K", 1, False, 1)], "W": []})
    inv = [(("B", "P"), 2), (("B", "+P"), 2), (("W", "P"), 2), (("W", "+P"), 2), (("B", "K"), 1)]
    for level in ("I3", "file"):
        print("  pawn files", level, _uniformity(setup, inv, level, False))


def test_uniform_lance_file():
    slots = [Slot("BL", "B", "L", 1), Slot("BRC", "B", "RC", 2), Slot("BP", "B", "P", 3), Slot("WP", "W", "P", 5)]
    setup = Setup(1, 6, 2, [slots], {"B": [], "W": []})
    inv = [((s.colour, pre + s.kind), 1) for s in slots for pre in ("", "+")]
    print("  lance file", _uniformity(setup, inv, "file", False, per_board=25))


def test_uniform_colour():
    setup = Setup(2, 3, 1, [[Slot("BP", "B", "P", 1)], []],
                  {"B": [Bound("B", (0, 1)), Jumper("O", "N", 1)], "W": [Std("K", 1, False, 1)]})
    inv = [(("B", "P"), 1), (("B", "+P"), 1), (("B", "B"), 2), (("B", "+B"), 2),
           (("B", "O"), 1), (("B", "N"), 2), (("W", "K"), 1)]
    print("  colour", _uniformity(setup, inv, "file", True, per_board=25))


def test_chu_primary():
    setup = chu_setup("file", **PRIMARY)
    s = Sampler(setup, "file", True)
    assert s.total == count(setup, "file", colour=True).total
    rng = random.Random(1)
    for _ in range(300):
        board, info = s.sample(rng)
        assert is_candidate(setup, board, "file", True)
        back, turn, flag = parse(to_sfen(board))
        assert back == board
    print("  chu primary: 300 samples ok")


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print("ok", name)
