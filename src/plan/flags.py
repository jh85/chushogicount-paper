#!/usr/bin/env python3
"""Effective counter-strike flags of a candidate board (decision D3).

A flag square l is *realizable* for a Black-to-move board if White's last move
could have been a non-lion capturing a Black lion on l: the White piece now on l
(or, for an igui / pass-through of a horned falcon or soaring eagle, the empty
square l it captured on) has an empty origin square from which that capture was
a legal move, with promotion on the capture allowed by the zone rule, and Black
could have had one more lion (I9).  The flag is *effective* if it bans at least
one Black move: Black has a non-lion that can capture a White lion on a square
other than l.  Two flags are the same state when they ban the same moves.

effective_states(board) -> list of (l, banned squares) with distinct banned
sets; its length is the number of extra states the board carries.

Static necessary conditions only: a flag state still needs a certificate.

Usage: python3 src/plan/flags.py --n 10000000 --seed 11 --procs 16
estimates the share of boards with >= 1 effective state and the mean number of
extra states, overall and by terminal / non-terminal stratum.
"""
import argparse
import math
import random
import sys
from collections import Counter
from multiprocessing import Pool
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from plan.moves import SQUARES, in_zone, single_moves          # noqa: E402

# roles a White piece now on l may have had before the capturing move
PRIOR = {"+P": "P", "+GB": "GB", "+L": "L", "+RC": "RC", "+M": "M", "+V": "V", "+C": "C",
         "+S": "S", "+F": "F", "+T": "T", "+G": "G", "+B": "B", "+R": "R", "+H": "H",
         "+D": "D", "K": "E", "N": "O", "Q": "X"}


def _single_moves_geo(board, sq, piece, geo):
    """plan.moves.single_moves on the board of a Geometry (validation variants)."""
    from plan.moves import MOVES
    colour, role = piece
    sign = 1 if colour == "B" else -1
    steps, slides = MOVES[role]
    out = []
    for dx, dy in steps:
        t = (sq[0] + dx, sq[1] + dy * sign)
        if geo.on(t) and (t not in board or board[t][0] != colour):
            out.append(t)
    for dx, dy in slides:
        t = (sq[0] + dx, sq[1] + dy * sign)
        while geo.on(t):
            if t in board:
                if board[t][0] != colour:
                    out.append(t)
                break
            out.append(t)
            t = (t[0] + dx, t[1] + dy * sign)
    return out


def _origins(board, piece, dest, geo=None):
    """Empty squares from which `piece` could have moved to capture on dest.
    geo (plan.lanes.Geometry) selects a variant's board; None is chu shogi."""
    colour, role = piece
    probe = dict(board)
    probe[dest] = ("B" if colour == "W" else "W", "K")        # a capturable dummy
    squares = SQUARES if geo is None else [(x, r) for x in range(geo.nf) for r in range(1, geo.nr + 1)]
    out = []
    for a in squares:
        if a in board:
            continue
        probe[a] = piece
        dests = single_moves(probe, a, piece) if geo is None else _single_moves_geo(probe, a, piece, geo)
        if dest in dests:
            out.append(a)
        del probe[a]
    return out


_SETUP = None


def _predecessor_ok(board, l, prior_piece, origin, after_sq=None, setup=None, colour=True, lanes=False):
    """Is the position before the capture a candidate (static filter)?  The
    Black lion stands on l, the capturer (with its role before the move) on
    origin; for an igui/pass-through the capturer now on after_sq is moved.
    setup: a validation variant's Setup (None: chu shogi); colour: its I6/I7
    mode; lanes: also require I10 (lane_ok) of the predecessor."""
    global _SETUP
    if setup is None:
        if _SETUP is None:
            from count.candidates import chu_setup
            _SETUP = chu_setup("file", identify_royals=True)
        setup, colour = _SETUP, True
    from count.candidates import is_candidate
    P = dict(board)
    P.pop(after_sq if after_sq is not None else l, None)
    P[origin] = prior_piece
    P[l] = ("B", "N")
    if not is_candidate(setup, P, "file", colour):
        return False
    if lanes:
        from plan.lanes import Geometry, lane_ok
        return lane_ok(P, Geometry(setup))
    return True


def _variant_roles(setup):
    """Roles that can appear on a variant's board."""
    roles = set()
    for c in "BW":
        for g in setup.free[c]:
            roles |= set(g.roles())
    for f in setup.files:
        for s in f:
            roles |= {s.kind, "+" + s.kind}
    return roles


def _realizable_flags_variant(board, setup, colour, lanes):
    """realizable_flags for a validation variant (board of setup's geometry;
    no falcon/eagle pass-through, as the variants have none)."""
    from count.candidates import Std
    from plan.lanes import Geometry
    from plan.moves import PROMOTES
    geo = Geometry(setup)
    if not any(p == ("B", "K") for p in board.values()):
        return {}                                   # terminal: no move follows
    max_lions = sum(g.n for g in setup.free["B"] if isinstance(g, Std) and g.name == "N")
    lions_b = sum(1 for p in board.values() if p == ("B", "N"))
    if lions_b + 1 > max_lions:
        return {}                                   # Black could not have had another lion
    roles = _variant_roles(setup)
    prior_of = {PROMOTES[r]: r for r in roles if r in PROMOTES and PROMOTES[r] in roles}
    out = {}
    for l, (c, role) in board.items():
        if c != "W":
            continue
        priors = []
        if role != "N":
            priors.append((role, False))            # unchanged role
        if role in prior_of:                        # promoted on the capture
            priors.append((prior_of[role], True))
        for prior, promoted in priors:
            for a in _origins(board, ("W", prior), l, geo):
                if promoted and not (geo.in_zone("W", l) or geo.in_zone("W", a)):
                    continue
                if not _predecessor_ok(board, l, ("W", prior), a, setup=setup, colour=colour, lanes=lanes):
                    continue
                out.setdefault(l, []).append(((c, prior), a))
    return out


def realizable_flags(board, setup=None, colour=True, lanes=False):
    """Squares l on which White's last move may have taken a Black lion with a
    non-lion (Black to move now).  Returns {l: [(prior_piece, origin), ...]}:
    the capturer's role before the move and its origin square.  The position
    before the capture must itself be a candidate (added 2026-10-06; before
    that, e.g. a kirin promoting on the capture could be placed off its colour).
    With setup (a validation variant's Setup, docs/validation-variant.md) the
    same predicate on that variant's board (colour: its I6/I7 mode; lanes: also
    require I10 of the predecessor); the chu path below is unchanged."""
    if setup is not None:
        return _realizable_flags_variant(board, setup, colour, lanes)
    if not any(p == ("B", "K") for p in board.values()):
        return {}                                   # terminal: no move follows
    lions_b = sum(1 for p in board.values() if p == ("B", "N"))
    kirin_b = sum(1 for p in board.values() if p == ("B", "O"))
    if lions_b + 1 + kirin_b > 2:
        return {}                                   # Black could not have had another lion
    out = {}
    for l, (c, role) in board.items():
        if c != "W":
            continue
        priors = []
        if role != "N":
            priors.append((role, False))            # unchanged role
        if role in PRIOR:                           # promoted on the capture
            priors.append((PRIOR[role], True))
        for prior, promoted in priors:
            for a in _origins(board, ("W", prior), l):
                if promoted and not (in_zone("W", l) or in_zone("W", a)):
                    continue
                if not _predecessor_ok(board, l, ("W", prior), a):
                    continue
                out.setdefault(l, []).append(((c, prior), a))
    # igui / pass-through by a horned falcon (straight ahead) or soaring eagle (diagonals)
    for q, (c, role) in board.items():
        if c != "W" or role not in ("+H", "+D"):
            continue
        dirs = [(0, -1)] if role == "+H" else [(1, -1), (-1, -1)]
        for dx, dy in dirs:
            mid = (q[0] + dx, q[1] + dy)             # igui: it returned to q, took on mid
            if mid in SQUARES and mid not in board and _predecessor_ok(board, mid, (c, role), q, after_sq=q):
                out.setdefault(mid, []).append(((c, role), q))
            mid2 = (q[0] - dx, q[1] - dy)            # pass-through: origin two steps back
            a = (q[0] - 2 * dx, q[1] - 2 * dy)
            if mid2 in SQUARES and mid2 not in board and a in SQUARES and a not in board \
                    and _predecessor_ok(board, mid2, (c, role), a, after_sq=q):
                out.setdefault(mid2, []).append(((c, role), a))
    return out


def black_non_lion_lion_captures(board):
    """Squares of White lions that some Black non-lion piece can capture."""
    targets = set()
    for sq, (c, role) in board.items():
        if c != "B" or role == "N":
            continue
        for t in single_moves(board, sq):
            if board.get(t) == ("W", "N"):
                targets.add(t)
    return targets


def effective_states(board):
    flags = realizable_flags(board)
    if not flags:
        return []
    att = black_non_lion_lion_captures(board)
    if not att:
        return []
    seen, out = set(), []
    for l in flags:
        banned = frozenset(att - {l})
        if banned and banned not in seen:
            seen.add(banned)
            out.append((l, banned))
    return out


def terminal_realizations(board):
    """For a terminal board (Black has no royal): White pieces that could have
    just captured Black's last royal, as [(prior_piece, square, origin)].  Empty
    means the board is proven unreachable."""
    if any(p == ("B", "K") for p in board.values()):
        return []
    out = []
    for s, (c, role) in board.items():
        if c != "W":
            continue
        priors = [(role, False)] + ([(PRIOR[role], True)] if role in PRIOR else [])
        for prior, promoted in priors:
            for a in _origins(board, ("W", prior), s):
                if promoted and not (in_zone("W", s) or in_zone("W", a)):
                    continue
                P = dict(board)
                del P[s]
                P[a] = ("W", prior)
                P[s] = ("B", "K")
                if _SETUP is None:
                    _predecessor_ok(board, s, ("W", prior), a)      # initialises _SETUP
                from count.candidates import is_candidate
                if not is_candidate(_SETUP, P, "file", True):
                    continue
                out.append((("W", prior), s, a))
    return out


# --- estimation -------------------------------------------------------------
_S = None


_JCSA = False
_ENG = None


def _init(seed, jcsa=False):
    global _S, _JCSA, _ENG
    from count.candidates import PRIMARY, chu_setup
    from count.sampler import Sampler
    _S = Sampler(chu_setup("file", **PRIMARY), "file", True)
    _JCSA = jcsa
    if jcsa:
        from plan.engine import Engine
        _ENG = Engine()


def _work(args):
    """Counter over (terminal, k) — or, with --jcsa, over (terminal, k_lishogi, k_jcsa)
    on the same boards (paired; docs/jcsa-delta.md)."""
    seed, n = args
    rng = random.Random(seed)
    c = Counter()
    for _ in range(n):
        board, info = _S.sample(rng)
        terminal = not any(p == ("B", "K") for p in board.values())
        if _JCSA:
            from jcsa.flags_jcsa import effective_states_both
            kl, kj = effective_states_both(_ENG, board) if not terminal else (0, 0)
            c[(terminal, kl, kj)] += 1
        else:
            k = len(effective_states(board))
            c[(terminal, k)] += 1
    return c


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=100000)
    ap.add_argument("--seed", type=int, default=11)
    ap.add_argument("--procs", type=int, default=16)
    ap.add_argument("--jcsa", action="store_true", help="paired lishogi / JCSA effective-state counts (engine per worker)")
    args = ap.parse_args()
    chunks = max(64, args.n // 20000)
    per = args.n // chunks
    with Pool(args.procs, initializer=_init, initargs=(args.seed, args.jcsa)) as pool:
        total = Counter()
        for i, c in enumerate(pool.imap_unordered(_work, [(args.seed * 100000 + i, per) for i in range(chunks)])):
            total.update(c)
            if (i + 1) % 50 == 0:
                n = sum(total.values())
                print(f"  ... {n} boards, mean extra states {sum(key[1] * v for key, v in total.items()) / n:.5f}", flush=True)
    if args.jcsa:
        n = sum(total.values())
        nt = sum(v for key, v in total.items() if not key[0])
        el = sum(kl * v for (t, kl, kj), v in total.items() if not t)
        ej = sum(kj * v for (t, kl, kj), v in total.items() if not t)
        d = sum((kl - kj) * v for (t, kl, kj), v in total.items() if not t)
        d2 = sum((kl - kj) ** 2 * v for (t, kl, kj), v in total.items() if not t)
        se = math.sqrt(max(d2 / nt - (d / nt) ** 2, 0) / nt)
        print(f"boards: {n}  (seed {args.seed}); non-terminal {nt}")
        print(f"  E[k] lishogi {el / nt:.5f}  E[k] JCSA {ej / nt:.5f}  paired difference {d / nt:.5f} ± {3 * se:.5f} (3σ)")
        print(f"  by (k_lishogi, k_jcsa): {dict(sorted(((kl, kj), v) for (t, kl, kj), v in total.items() if not t))}")
        return
    n = sum(total.values())
    print(f"boards: {n}  (seed {args.seed})")
    for strat, name in ((False, "non-terminal"), (True, "terminal")):
        m = sum(v for (t, k), v in total.items() if t == strat)
        if not m:
            continue
        ge1 = sum(v for (t, k), v in total.items() if t == strat and k >= 1)
        extra = sum(k * v for (t, k), v in total.items() if t == strat)
        p = ge1 / m
        print(f"  {name:13s} n={m}  share with >=1 effective flag {p:.5f} ± {3 * math.sqrt(p * (1 - p) / m):.5f} (3σ)"
              f"  mean extra states {extra / m:.5f}  by k: {dict(sorted((k, v) for (t, k), v in total.items() if t == strat))}")
    extra = sum(k * v for (t, k), v in total.items())
    print(f"  overall mean extra states per board {extra / n:.5f}")


if __name__ == "__main__":
    main()
