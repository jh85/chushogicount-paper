#!/usr/bin/env python3
"""Tests for src/count.  Run: python3 tests/test_count.py   (or pytest tests/)

1. filegame: the exhaustive per-file search agrees with the hand-written
   invariants of docs/invariants.md (I1-I4 exactly, I5 in its sharpened form).
2. candidates: the generating-function count equals a brute-force enumeration
   of boards filtered by is_candidate, on small boards.
3. chu shogi: regression values (brief section 6) and internal consistency.
"""
import itertools
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))
from count import filegame                                              # noqa: E402
from count.candidates import (Bound, Jumper, Royal, Setup, Std, chu_setup, count,  # noqa: E402
                              count_chu, is_candidate)
from count.filegame import Slot                                         # noqa: E402

R, Z = 12, 4
BOUNDS = {"BP": (4, 12), "WP": (1, 9)}
MIRROR = {"BL": "WL", "WL": "BL", "BRC": "WRC", "WRC": "BRC",
          "BP": "WP", "WP": "BP", "BGB": "WGB", "WGB": "BGB"}


def hand_eligible(names, u, n):
    """Sharpened I5 (docs/invariants.md): may slot n have promoted, given the
    unpromoted pieces u (rank or 0 per slot) of its file?"""
    rank = lambda m: u[names.index(m)] if m in names else 0
    if n in ("BP", "WP"):                                   # I4
        return not rank("BP") and not rank("WP")
    if n[0] == "W":                                         # colour symmetry
        return hand_eligible([MIRROR[m] for m in reversed(names)],
                             tuple(R + 1 - r if r else 0 for r in reversed(u)), MIRROR[n])
    if rank("WP"):
        return False
    if n == "BGB":
        return True
    above = [m for m in {"BL": ["BRC", "BP", "WRC", "WL"], "BRC": ["BP", "WRC", "WL"]}[n] if rank(m)]
    if (R - Z + 1) + len(above) > R:                        # no room above rank 9
        return False
    if rank("BP"):                                          # own pawn must already be past
        return rank("BP") >= (R - Z + 1) + 1 + int(n == "BL" and rank("BRC") > 0)
    return True


def test_filegame_matches_hand_invariants():
    for x in (1, 3, 0):
        slots = filegame.chu_file_slots(x)
        names = [s.name for s in slots]
        adm = filegame.admissible(slots, R, Z)
        # I1-I3: U-configs are exactly the increasing rank sequences within bounds
        hand = set()
        for ranks in itertools.product(*[[0] + list(range(*(lambda b: (b[0], b[1] + 1))(BOUNDS.get(n, (1, R)))))
                                         for n in names]):
            on = [r for r in ranks if r]
            if all(a < b for a, b in zip(on, on[1:])):
                hand.add(ranks)
        assert hand == set(adm), x
        pawns = {names.index("BP"), names.index("WP")}
        for u, fam in adm.items():
            single = {i for i in range(len(slots)) if frozenset([i]) in fam}
            assert single == {i for i, n in enumerate(names) if not u[i] and hand_eligible(names, u, n)}
            # product structure: any set of eligible non-pawns, plus at most one pawn
            want = set()
            rest = sorted(single - pawns)
            for k in range(len(rest) + 1):
                for c in itertools.combinations(rest, k):
                    want.add(frozenset(c))
                    want.update(frozenset(c) | {p} for p in single & pawns)
            assert want == fam, (x, u)


def brute(setup, inventory, level, colour):
    squares = [(x, r) for x in range(setup.nfiles) for r in range(1, setup.nranks + 1)]
    left = [m for _, m in inventory]
    board = {}

    def rec(i):
        if i == len(squares):
            return int(is_candidate(setup, board, level, colour))
        tot = rec(i + 1)
        for k, (piece, _) in enumerate(inventory):
            if left[k]:
                left[k] -= 1
                board[squares[i]] = piece
                tot += rec(i + 1)
                del board[squares[i]]
                left[k] += 1
        return tot
    return rec(0)


def _check(setup, inventory, colours=(False,)):
    for level in ("I3", "I4", "I5", "file"):
        for colour in colours:
            got = count(setup, level, colour, stats=True)
            assert got.total == brute(setup, inventory, level, colour), (level, colour)
            assert sum(got.by_pawns.values()) == got.total


def _inv(*roles):
    return [((c, r), m) for c, r, m in roles]


def test_micro_two_pawn_files():
    f = [Slot("BP", "B", "P", 1), Slot("WP", "W", "P", 3)]
    setup = Setup(2, 3, 1, [f, f], {"B": [], "W": []})
    _check(setup, _inv(("B", "P", 2), ("B", "+P", 2), ("W", "P", 2), ("W", "+P", 2)))


def test_micro_two_lance_files():
    f = [Slot("BL", "B", "L", 1), Slot("BP", "B", "P", 2)]
    setup = Setup(2, 4, 2, [f, f], {"B": [], "W": []})
    _check(setup, _inv(("B", "L", 2), ("B", "+L", 2), ("B", "P", 2), ("B", "+P", 2)))


def test_micro_lance_chariot_file():
    for slots in ([Slot("BL", "B", "L", 1), Slot("BRC", "B", "RC", 2), Slot("BP", "B", "P", 3),
                   Slot("WP", "W", "P", 5)],
                  [Slot("BP", "B", "P", 2), Slot("WP", "W", "P", 4), Slot("WRC", "W", "RC", 5),
                   Slot("WL", "W", "L", 6)],
                  [Slot("BP", "B", "P", 2), Slot("BGB", "B", "GB", 3), Slot("WGB", "W", "GB", 4),
                   Slot("WP", "W", "P", 5)]):
        setup = Setup(1, 6, 2, [slots], {"B": [], "W": []})
        inv = [((s.colour, pre + s.kind), 1) for s in slots for pre in ("", "+")]
        _check(setup, inv)


def test_micro_colour():
    setup = Setup(2, 3, 1, [[Slot("BP", "B", "P", 1)], []],
                  {"B": [Bound("B", (0, 1)), Jumper("O", "N", 1)], "W": []})
    _check(setup, _inv(("B", "P", 1), ("B", "+P", 1), ("B", "B", 2), ("B", "+B", 2),
                       ("B", "O", 1), ("B", "N", 2)), colours=(False, True))


def test_micro_identified_royals():
    # D2: crown prince written as 'K'.  King alone and crown prince alone give the same
    # board and must be counted once (they were counted twice until 2026-10-16).
    for required in (True, False):
        setup = Setup(2, 2, 1, [[], []], {"B": [Royal(required, identify=True), Std("G", 1, promotable=False)],
                                          "W": [Royal(True, identify=True)]})
        inv = _inv(("B", "K", 2), ("B", "E", 1), ("B", "G", 1), ("W", "K", 2), ("W", "E", 1))
        _check(setup, inv)
    assert count(Setup(1, 1, 1, [[]], {"B": [Royal(True, identify=True)], "W": []}), "file").total == 1


def test_chu_regression():
    # brief section 6 (float64 there): 6.70e181, 1.50e176, 5.60e165, 1.00e165
    want = {"naive": "6.6993e181", "I3": "1.5027e176", "I4": "5.6029e165", "I5": "1.0032e165",
            "file": "9.9965e164"}
    for level, w in want.items():
        v = count_chu(level).total
        assert f"{v / 10 ** (len(str(v)) - 1):.4f}e{len(str(v)) - 1}" == w, level
    c5 = count_chu("I5", stats=True, dist=True)
    assert sum(c5.by_pieces.values()) == c5.total == sum(c5.by_pawns.values())
    assert max(c5.by_pieces, key=c5.by_pieces.get) == 80
    assert abs(c5.mean_pieces - sum(n * v for n, v in c5.by_pieces.items()) / c5.total) < 1e-9


def test_chu_colour_bookkeeping():
    # With no colour-bound piece, tracking square colours must not change the count.
    setup = chu_setup()
    for c in "BW":
        setup.free[c] = [Std("B", 2) if isinstance(g, Bound) else
                         Jumper(g.uname, g.pname) if isinstance(g, Jumper) else g for g in setup.free[c]]
    assert count(setup, "file", colour=True).total == count_chu("file").total
    full = count_chu("file", colour=True).total
    assert f"{full / 10 ** 164:.4f}" == "3.4351"


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
            print("ok", name)
