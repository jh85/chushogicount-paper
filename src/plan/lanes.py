"""I10 (candidate necessary condition, 2026-10-06): every non-wall piece needs an
entrance that no pawn/lance trajectory covers.

A wall (unpromoted pawn or lance) occupies, at every moment of the game, a square
of its trajectory: the squares of its file between its start square and its
present square, inclusive.  A non-wall piece P now on s arrived on s at some
moment (as P, or as the piece it promoted from if s lies in its promotion zone);
at that moment s was empty, P stood on an entrance square e, and for a sliding
move the squares between e and s were empty.  So some wall-free choice must
exist: an entrance (e, path) such that no wall's trajectory is contained in
{s, e} ∪ path.  (Walls of one file have disjoint ordered trajectories, so the
other walls can always stand elsewhere.)  Jumps and lion-power moves need no
path.  The condition is purely local and cheap.
"""
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from plan.moves import MOVES                                   # noqa: E402

WALLS = ("P", "L")
START_RANK = {("B", "P"): 4, ("W", "P"): 9, ("B", "L"): 1, ("W", "L"): 12}   # chu shogi


class Geometry:
    """Board size, start ranks of the walls (per file) and promotion zone of a
    Setup, so that I10 can be checked on validation variants too."""

    def __init__(self, setup=None):
        if setup is None:
            self.nf, self.nr, self.zone = 12, 12, 4
            self.start = {}
        else:
            self.nf, self.nr, self.zone = setup.nfiles, setup.nranks, setup.zone
            self.start = {(x, sl.colour, sl.kind): sl.start for x, f in enumerate(setup.files) for sl in f}

    def start_rank(self, x, colour, kind):
        if (x, colour, kind) in self.start:
            return self.start[(x, colour, kind)]
        return START_RANK[(colour, kind)]

    def on(self, sq):
        return 0 <= sq[0] < self.nf and 1 <= sq[1] <= self.nr

    def in_zone(self, colour, sq):
        return sq[1] > self.nr - self.zone if colour == "B" else sq[1] <= self.zone


CHU = Geometry()
UNPROMOTED = {v: k for k, v in {"P": "+P", "GB": "+GB", "L": "+L", "RC": "+RC", "M": "+M", "V": "+V",
                                "C": "+C", "S": "+S", "F": "+F", "T": "+T", "G": "+G", "E": "K",
                                "B": "+B", "R": "+R", "H": "+H", "D": "+D", "O": "N", "X": "Q"}.items()}


def trajectories(board, geo=CHU):
    out = []
    for sq, (c, role) in board.items():
        if role in WALLS:
            r0, r1 = geo.start_rank(sq[0], c, role), sq[1]
            out.append(frozenset((sq[0], r) for r in range(min(r0, r1), max(r0, r1) + 1)))
    return out


def entrances_with_paths(sq, piece, geo=CHU):
    """[(e, path squares)] for every single move of `piece` ending on sq, on an
    otherwise empty board."""
    colour, role = piece
    sign = 1 if colour == "B" else -1
    steps, slides = MOVES[role]
    out = []
    for dx, dy in steps:
        e = (sq[0] - dx, sq[1] - dy * sign)
        if geo.on(e):
            out.append((e, []))
    for dx, dy in slides:
        e, path = (sq[0] - dx, sq[1] - dy * sign), []
        while geo.on(e):
            out.append((e, list(path)))
            path.append(e)
            e = (e[0] - dx, e[1] - dy * sign)
    return out


def lane_ok_piece(board, sq, piece, trajs=None, geo=CHU):
    colour, role = piece
    if role in WALLS:
        return True
    trajs = trajectories(board, geo) if trajs is None else trajs
    forms = [piece]
    if role in UNPROMOTED and geo.in_zone(colour, sq):
        forms.append((colour, UNPROMOTED[role]))        # arrived unpromoted and promoted on sq
    for form in forms:
        for e, path in entrances_with_paths(sq, form, geo):
            S = {sq, e} | set(path)
            if not any(t <= S for t in trajs):
                return True
    return False


def lane_ok(board, geo=CHU):
    trajs = trajectories(board, geo)
    return all(lane_ok_piece(board, sq, piece, trajs, geo) for sq, piece in board.items())


def violations(board, geo=CHU):
    trajs = trajectories(board, geo)
    return [(sq, piece) for sq, piece in board.items() if not lane_ok_piece(board, sq, piece, trajs, geo)]


_SAMPLERS = {}   # one Sampler per (worker process, stratum); see _sampler


def _sampler(terminal):
    """Build the stratum's Sampler once per worker process.

    A fresh Sampler per task leaked ~0.73 GB per task (its lru_cache'd methods keep the
    instance alive); 14 workers × many 20 000-board chunks exhausted the 62 GB box on
    2026-10-06. The pool is recreated per stratum, so each worker holds one Sampler.
    """
    from count.candidates import chu_setup
    from count.sampler import Sampler
    if terminal not in _SAMPLERS:
        _SAMPLERS[terminal] = Sampler(chu_setup("file", identify_royals=True, terminal_only=terminal), "file", True)
    return _SAMPLERS[terminal]


def _share_worker(args):
    import random
    from plan.flags import effective_states
    seed, n, terminal = args
    s = _sampler(terminal)
    rng = random.Random(seed)
    bad = flag_states_bad = 0
    for _ in range(n):
        b = s.sample(rng)[0]
        if not lane_ok(b):
            bad += 1
            if not terminal:
                flag_states_bad += len(effective_states(b))
    return bad, flag_states_bad


def main():
    import argparse
    import math
    from multiprocessing import Pool
    ap = argparse.ArgumentParser(description="share of candidate boards violating I10, per stratum")
    ap.add_argument("--n", type=int, default=100000)
    ap.add_argument("--seed", type=int, default=17)
    ap.add_argument("--procs", type=int, default=8)
    a = ap.parse_args()
    for terminal, name in ((False, "non-terminal"), (True, "terminal")):
        chunks = max(a.procs, a.n // 20000)
        per = a.n // chunks
        with Pool(a.procs) as pool:
            res = pool.map(_share_worker, [(a.seed * 7919 + i + (10 ** 6 if terminal else 0), per, terminal) for i in range(chunks)])
        bad, fbad = sum(r[0] for r in res), sum(r[1] for r in res)
        n = per * chunks
        p = bad / n
        print(f"{name}: {bad}/{n} violate I10: share {p:.5f} ± {3 * math.sqrt(p * (1 - p) / n):.5f} (3σ)"
              + (f"; effective-flag states on violating boards: {fbad} ({fbad / n:.5f} per board)" if not terminal else ""), flush=True)


if __name__ == "__main__":
    main()
