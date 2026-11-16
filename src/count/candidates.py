#!/usr/bin/env python3
"""Exact (big-integer) size of chu shogi candidate sets.

A candidate is a board (no side to move, no lion flag) that passes a chosen list of
static necessary conditions.  See docs/invariants.md for the conditions and their
proofs, docs/spec.md for coordinates and docs/decisions.md for the provisional
state conventions (the defaults below).

Levels (cumulative):
  naive  material limits only, every piece anywhere (paper-style candidate set)
  I3     + I1-I3: unpromoted pawn/lance/reverse chariot/go-between on their file,
           in start order, pawns never behind their start rank
  I4     + promoted pawns: T_B + T_W <= number of files with no unpromoted pawn
  I5     + the brief's per-file capacity for promoted lance/chariot/go-between
  file   exact per-file admissibility from the abstract file game (filegame.py);
           equals I1-I4 plus a sharpened I5
colour=True adds I6/I7 (colour-bound unpromoted bishops and kirins).

Method.  Unpromoted confined pieces are enumerated file by file and summarised by
a small feature vector; every other piece is "free" and is counted by exponential
generating functions.  All arithmetic is exact (int / Fraction).

Usage:  python3 src/count/candidates.py [--all | --level L [--colour]] [--royal MODE]
"""
import argparse
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count import filegame                                    # noqa: E402
from count.filegame import Slot                                # noqa: E402

LEVELS = ("naive", "I3", "I4", "I5", "file")
CONFINED = ("P", "L", "RC", "GB")


# ---------------------------------------------------------------------------
# Free-piece groups.  states(colour) lists the group's states as
# (m, div, a0, a1, free, bound): m pieces that may stand on any free square,
# weight 1/div for identical pieces, a0/a1 pieces forced onto colour class 0/1;
# `free` lists the m pieces and `bound` the forced ones per class (used by the
# sampler).  terms(colour) is the same without the piece lists.
# ok(n, squares, colour) is the same condition as a predicate on one side's pieces:
# n(role) is the number on the board and squares(role) their (x, r) squares.
# ---------------------------------------------------------------------------
def sq_class(sq):
    return (sq[0] + sq[1]) % 2


class Group:
    def terms(self, colour):
        for st in self.states(colour):
            yield st[:4]


@dataclass(frozen=True)
class Std(Group):
    """n identical pieces, each captured / unpromoted / promoted ('+name')."""
    name: str
    n: int
    promotable: bool = True
    minimum: int = 0

    def roles(self):
        return (self.name, "+" + self.name) if self.promotable else (self.name,)

    def states(self, colour):
        for u in range(self.n + 1):
            for p in range(self.n - u + 1 if self.promotable else 1):
                if u + p >= self.minimum:
                    yield (u + p, factorial(u) * factorial(p), 0, 0,
                           [self.name] * u + ["+" + self.name] * p, {0: [], 1: []})

    def ok(self, n, squares, colour):
        u, p = n(self.name), n("+" + self.name)
        return self.minimum <= u + p <= self.n and (self.promotable or p == 0)


@dataclass(frozen=True)
class Bound(Group):
    """Colour-bound promotable pieces, one per entry of start_classes (I6)."""
    name: str
    start_classes: tuple

    def roles(self):
        return self.name, "+" + self.name

    def states(self, colour):
        n = len(self.start_classes)
        if not colour:
            yield from Std(self.name, n).states(False)
            return
        s0, s1 = self.start_classes.count(0), self.start_classes.count(1)
        for u0 in range(s0 + 1):
            for u1 in range(s1 + 1):
                for p in range(n - u0 - u1 + 1):
                    yield (p, factorial(u0) * factorial(u1) * factorial(p), u0, u1,
                           ["+" + self.name] * p, {0: [self.name] * u0, 1: [self.name] * u1})

    def ok(self, n, squares, colour):
        if n(self.name) + n("+" + self.name) > len(self.start_classes):
            return False
        if colour:
            on = [sq_class(s) for s in squares(self.name)]
            return all(on.count(c) <= self.start_classes.count(c) for c in (0, 1))
        return True


@dataclass(frozen=True)
class Jumper(Group):
    """One `uname` (kirin/phoenix) promoting to `pname`, plus one native `pname`
    (lion/free king); the promoted piece is identified with the native one.
    bound_class: colour class the unpromoted piece is bound to (I7), or None."""
    uname: str
    pname: str
    bound_class: object = None

    def roles(self):
        return self.uname, self.pname

    def states(self, colour):
        for k in (0, 1):
            for big in range(3 - k):
                if colour and self.bound_class is not None:
                    bound = {0: [], 1: []}
                    bound[self.bound_class] = [self.uname] * k
                    yield (big, factorial(big), k * (self.bound_class == 0),
                           k * (self.bound_class == 1), [self.pname] * big, bound)
                else:
                    yield (k + big, factorial(big), 0, 0,
                           [self.uname] * k + [self.pname] * big, {0: [], 1: []})

    def ok(self, n, squares, colour):
        k = n(self.uname)
        if k > 1 or k + n(self.pname) > 2:
            return False
        if colour and self.bound_class is not None:
            return all(sq_class(s) == self.bound_class for s in squares(self.uname))
        return True


@dataclass(frozen=True)
class Royal(Group):
    """King K, drunk elephant E, crown prince +E.  required: the side has a royal.
    identify: crown prince written as a second 'K' (D2)."""
    required: bool = True
    identify: bool = False

    def roles(self):
        return ("K", "E") if self.identify else ("K", "E", "+E")

    def _states(self):
        for k in (0, 1):
            for e, cp in ((0, 0), (1, 0), (0, 1)):
                if k + cp >= 1 or not self.required:
                    yield k, e, cp

    def states(self, colour):
        seen = set()
        for k, e, cp in self._states():
            if self.identify:
                # king alone and crown prince alone are the same board: one 'K'
                # (yielding both counted every such side twice; fixed 2026-10-16)
                if (k + cp, e) in seen:
                    continue
                seen.add((k + cp, e))
                yield k + e + cp, factorial(k + cp), 0, 0, ["K"] * (k + cp) + ["E"] * e, {0: [], 1: []}
            else:
                yield k + e + cp, 1, 0, 0, ["K"] * k + ["E"] * e + ["+E"] * cp, {0: [], 1: []}

    def ok(self, n, squares, colour):
        if self.identify:
            return any((k + cp, e) == (n("K"), n("E")) for k, e, cp in self._states())
        return (n("K"), n("E"), n("+E")) in set(self._states())


@dataclass
class Setup:
    nfiles: int
    nranks: int
    zone: int
    files: list          # per file index, list of filegame.Slot
    free: dict           # 'B' / 'W' -> list of groups

    @property
    def nsquares(self):
        return self.nfiles * self.nranks


def chu_setup(level="file", mover_royal_required=True, identify_royals=False, lone=None,
              terminal_only=False):
    """Chu shogi with Black to move.  The side not to move (White) always has a
    royal; mover_royal_required=False also admits the terminal boards on which
    Black has none (D4).  identify_royals: crown prince = king (D2).
    lone='B'/'W': that side consists of a single royal and nothing else (bare-king
    bound, D4)."""
    def side(colour, required):
        if lone == colour:
            return [Std("K", 1, promotable=False, minimum=1)]
        kirin_class = 1                      # f2 and g11 both lie on class 1
        bishops = (0, 1)                     # c2/j2 and c11/j11: one per class
        g = [Royal(required, identify_royals)]
        g += [Std(n, 2) for n in ("G", "S", "C", "F", "T", "M", "V", "R", "H", "D")]
        g += [Bound("B", bishops), Jumper("O", "N", kirin_class), Jumper("X", "Q")]
        return g
    free = {"B": side("B", mover_royal_required), "W": side("W", True)}
    if terminal_only:                     # Black has no royal: only an unpromoted elephant may remain
        free["B"][0] = Std("E", 1, promotable=False)
    if level == "naive":
        for c in "BW":
            if lone != c:
                free[c] += [Std("P", 12), Std("GB", 2), Std("L", 2), Std("RC", 2)]
        files = [[] for _ in range(12)]
    else:
        files = [[s for s in filegame.chu_file_slots(x) if s.colour != lone] for x in range(12)]
    return Setup(12, 12, 4, files, free)


def chu_literal_setup():
    """All 39 roles distinct, as in lishogi's SFEN (secondary figure, D2)."""
    s = chu_setup("file", mover_royal_required=False)
    for c in "BW":
        g = [x for x in s.free[c] if not isinstance(x, Jumper)]
        s.free[c] = g + [Bound("O", (1,)), Std("N", 1, promotable=False),
                         Std("X", 1), Std("Q", 1, promotable=False)]
    return s


PRIMARY = dict(mover_royal_required=False, identify_royals=True)   # D2 + D4


# ---------------------------------------------------------------------------
# Per-file features
# ---------------------------------------------------------------------------
@lru_cache(maxsize=None)
def _admissible(slots, nranks, zone):
    return filegame.admissible(list(slots), nranks, zone)


def elig_types(setup):
    return sorted({(s.colour, s.kind) for f in setup.files for s in f if s.kind != "P"})


def file_features(setup, x, u, level, colour):
    """Features of U-config u (rank or 0 per slot) of file x, or None if the
    config is not admissible.  Returns (uPB, uPW, cb, cw, j, d0, d1, elig):
    cb/cw/j bound the promoted pawns this file can account for (Black, White,
    both together); d0/d1 count its unpromoted pieces per colour class; elig maps
    (colour, kind) -> 1 if that slot may have promoted."""
    slots = setup.files[x]
    fam = _admissible(tuple(slots), setup.nranks, setup.zone).get(tuple(u))
    if fam is None:
        return None
    idx = {(s.colour, s.kind): i for i, s in enumerate(slots)}
    present = lambda c, k: (c, k) in idx and u[idx[(c, k)]] > 0
    upb, upw = int(present("B", "P")), int(present("W", "P"))
    cb = int(("B", "P") in idx and not upb)
    cw = int(("W", "P") in idx and not upw)
    if level == "I3":
        j = cb + cw
    elif level == "file":
        cb = int(("B", "P") in idx and frozenset([idx[("B", "P")]]) in fam)
        cw = int(("W", "P") in idx and frozenset([idx[("W", "P")]]) in fam)
        j = int(cb or cw)
    else:
        j = int((cb or cw) and not upb and not upw)
    if j == 0:
        cb = cw = 0
    elig = {}
    for (c, k), i in idx.items():
        if k == "P":
            continue
        if u[i]:
            e = 0
        elif level in ("I3", "I4"):
            e = 1
        elif level == "I5":
            e = int(not present("W" if c == "B" else "B", "P"))
        else:
            e = int(frozenset([i]) in fam)
        elig[(c, k)] = e
    d = [0, 0]
    for r in u:
        if r:
            d[(x + r) % 2 if colour else 0] += 1
    return upb, upw, cb, cw, j, d[0], d[1], elig


def _file_table(setup, x, level, colour, stats, etypes):
    slots = setup.files[x]
    out = Counter()
    for u in _admissible(tuple(slots), setup.nranks, setup.zone):
        upb, upw, cb, cw, j, d0, d1, elig = file_features(setup, x, u, level, colour)
        if not stats:
            upb = upw = 0
        out[(upb, upw, cb, cw, j, d0, d1) + tuple(elig.get(t, 0) for t in etypes)] += 1
    return out


def _conv(a, b, mul=None):
    out = defaultdict(int) if mul is None else {}
    for ka, va in a.items():
        for kb, vb in b.items():
            k = tuple(p + q for p, q in zip(ka, kb))
            if mul is None:
                out[k] += va * vb
            else:
                out[k] = _padd(out.get(k), mul(va, vb))
    return out


def _padd(a, b):
    if a is None:
        return list(b)
    if len(a) < len(b):
        a = a + [0] * (len(b) - len(a))
    for i, v in enumerate(b):
        a[i] += v
    return a


def _pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


# ---------------------------------------------------------------------------
# Counting
# ---------------------------------------------------------------------------
@dataclass
class Result:
    total: int
    sum_pieces: int            # sum over candidates of the number of pieces
    by_pawns: dict             # (uPB, uPW) -> count   (only with stats=True)
    by_pieces: dict            # pieces on board -> count (only with dist=True)

    @property
    def mean_pieces(self):
        return self.sum_pieces / self.total


def _free_polys(setup, colour):
    """{(A0, A1): [labelled coefficient per number of unconstrained pieces]}"""
    poly = {(0, 0): [Fraction(1)]}
    for c in "BW":
        for g in setup.free[c]:
            gp = {}
            for m, div, a0, a1 in g.terms(colour):
                lst = gp.setdefault((a0, a1), [])
                lst.extend([Fraction(0)] * (m + 1 - len(lst)))
                lst[m] += Fraction(1, div)
            poly = _conv(poly, gp, _pmul)
    out = {}
    for tag, lst in poly.items():
        lab = [v * factorial(m) for m, v in enumerate(lst)]
        assert all(v.denominator == 1 for v in lab)
        out[tag] = [int(v) for v in lab]
    return out


def count(setup, level="file", colour=False, stats=False, dist=False):
    """Number of candidate boards of `setup` at `level` (not 'naive': build the
    naive set with chu_setup('naive'), whose files are empty)."""
    assert level in LEVELS[1:]
    etypes = elig_types(setup)
    nslots = Counter((s.colour, s.kind) for f in setup.files for s in f)

    # --- confined part: plain files (pawns only) and groups of special files ---
    plain = {(0,) * 7: 1}
    special = []                                   # [types, table with elig sums]
    for x, slots in enumerate(setup.files):
        tab = _file_table(setup, x, level, colour, stats, etypes)
        mine = {(s.colour, s.kind) for s in slots if s.kind != "P"}
        if not mine:
            plain = _conv(plain, {k[:7]: v for k, v in tab.items()})
            continue
        for grp in [g for g in special if g[0] & mine]:
            special.remove(grp)
            mine |= grp[0]
            tab = _conv(tab, grp[1])
        special.append([mine, tab])

    # promoted lance/chariot/go-between: per type at most cap pieces, EGF
    # sum_{t<=cap} x^t/t!, kept as integers scaled by nslots[type]!
    scale = 1
    spoly = {(0,) * 7: [1]}
    for types, tab in special:
        ptab = {}
        for key, w in tab.items():
            p = [w]
            for t, cap in zip(etypes, key[7:]):
                if t in types:
                    p = _pmul(p, [factorial(nslots[t]) // factorial(i) for i in range(cap + 1)])
            ptab[key[:7]] = _padd(ptab.get(key[:7]), p)
        for t in types:
            scale *= factorial(nslots[t])
        spoly = _conv(spoly, ptab, _pmul)
    merged = _conv(spoly, plain, lambda p, w: [w * v for v in p])

    # --- free part ---------------------------------------------------------
    free = _free_polys(setup, colour)
    if colour:
        cap0 = sum((x + r) % 2 == 0 for x in range(setup.nfiles) for r in range(1, setup.nranks + 1))
        cap1 = setup.nsquares - cap0
    else:
        cap0, cap1 = setup.nsquares, 0
    kmax = max(k[4] for k in merged) + max(len(p) for p in merged.values())

    @lru_cache(maxsize=None)
    def w_terms(tag, f):
        """[k][j] -> ways to choose squares and types for k promoted confined and
        j free pieces on f squares, without the k-side type count."""
        g = free[tag]
        return [[g[j] * comb(k + j, j) * comb(f, k + j) for j in range(len(g))] for k in range(kmax)]

    def falling(n, k):
        r = 1
        for i in range(k):
            r *= n - i
        return r

    @lru_cache(maxsize=None)
    def uu(d0, d1):
        f0, f1 = cap0 - d0, cap1 - d1
        tot, tot1 = [0] * kmax, [0] * kmax
        for (a0, a1) in free:
            ways = falling(f0, a0) * falling(f1, a1)
            if not ways:
                continue
            wt = w_terms((a0, a1), f0 + f1 - a0 - a1)
            for k in range(kmax):
                tot[k] += ways * sum(wt[k])
                tot1[k] += ways * sum(v * (a0 + a1 + k + j) for j, v in enumerate(wt[k]))
        return tot, tot1

    @lru_cache(maxsize=None)
    def tok(cb, cw, j):
        return [sum(comb(t, tb) for tb in range(t + 1) if tb <= cb and t - tb <= cw) for t in range(j + 1)]

    total = sum_n = 0
    by_pawns = defaultdict(int)
    acc = defaultdict(lambda: [0] * kmax)
    for (upb, upw, cb, cw, j, d0, d1), cpoly in merged.items():
        vec = [0] * kmax
        for t, tv in enumerate(tok(cb, cw, j)):
            for r, cv in enumerate(cpoly):
                vec[t + r] += tv * cv * (factorial(t + r) // factorial(t))
        u0, u1 = uu(d0, d1)
        tot = sum(v * a for v, a in zip(vec, u0))
        total += tot
        sum_n += (d0 + d1) * tot + sum(v * a for v, a in zip(vec, u1))
        by_pawns[(upb, upw)] += tot
        if dist:
            a = acc[(d0, d1)]
            for k, v in enumerate(vec):
                a[k] += v
    by_pieces = defaultdict(int)
    for (d0, d1), a in acc.items():
        f0, f1 = cap0 - d0, cap1 - d1
        for (a0, a1) in free:
            ways = falling(f0, a0) * falling(f1, a1)
            if not ways:
                continue
            wt = w_terms((a0, a1), f0 + f1 - a0 - a1)
            for k, v in enumerate(a):
                if v:
                    for jj, w in enumerate(wt[k]):
                        by_pieces[d0 + d1 + a0 + a1 + k + jj] += v * ways * w

    def exact(v):
        q, rem = divmod(v, scale)
        assert rem == 0
        return q

    return Result(exact(total), exact(sum_n),
                  {k: exact(v) for k, v in by_pawns.items()} if stats else {},
                  {k: exact(v) for k, v in sorted(by_pieces.items())})


def count_chu(level="file", colour=False, stats=False, dist=False, **setup_kw):
    setup = chu_setup(level, **setup_kw)
    return count(setup, "I3" if level == "naive" else level, colour, stats, dist)


# ---------------------------------------------------------------------------
# The same conditions as a predicate on one board (static filter; test oracle)
# ---------------------------------------------------------------------------
def is_candidate(setup, board, level="file", colour=False):
    """board: {(x, r): (colour, role)} with roles as in the group definitions,
    confined pieces 'P', 'L', 'RC', 'GB' and their promoted forms '+P', ..."""
    n = Counter(board.values())
    where = defaultdict(list)
    for sq, piece in board.items():
        where[piece].append(sq)
    known = {c: {r for g in setup.free[c] for r in g.roles()} for c in "BW"}
    caps = Counter()
    cb = cw = jj = 0
    for x, slots in enumerate(setup.files):
        idx = {(s.colour, s.kind): i for i, s in enumerate(slots)}
        u = [0] * len(slots)
        for r in range(1, setup.nranks + 1):
            piece = board.get((x, r))
            if piece and piece[1] in CONFINED and piece[1] not in known[piece[0]]:
                i = idx.get(piece)
                if i is None or u[i]:
                    return False                    # I1: not a slot of this file
                u[i] = r
        feats = file_features(setup, x, tuple(u), level, colour)
        if feats is None:
            return False                            # I2, I3
        cb, cw, jj = cb + feats[2], cw + feats[3], jj + feats[4]
        caps.update(feats[7])
    for (c, k), cap in caps.items():
        if n[(c, "+" + k)] > cap:
            return False                            # I5
    tb, tw = n[("B", "+P")], n[("W", "+P")]
    if any(s.kind == "P" for f in setup.files for s in f) and (tb > cb or tw > cw or tb + tw > jj):
        return False                                # I4
    for c in "BW":
        for g in setup.free[c]:
            if not g.ok(lambda role: n[(c, role)], lambda role: where[(c, role)], colour):
                return False
    return True


# ---------------------------------------------------------------------------
def _sci(v):
    return f"{Fraction(v, 10 ** (len(str(v)) - 1)).__float__():.3f}e+{len(str(v)) - 1}"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--level", choices=LEVELS, default="file")
    ap.add_argument("--colour", action="store_true", help="add I6/I7")
    ap.add_argument("--royal", choices=("both", "mover-optional"), default="both")
    ap.add_argument("--identify-royals", action="store_true")
    ap.add_argument("--all", action="store_true", help="print all candidate-count variants")
    ap.add_argument("--exact", action="store_true", help="also print the full integers")
    args = ap.parse_args()
    kw = dict(mover_royal_required=args.royal == "both", identify_royals=args.identify_royals)

    def show(label, res):
        print(f"{label:<46} {_sci(res.total)}   mean pieces {res.mean_pieces:.2f}")
        if args.exact:
            print(f"    = {res.total}")
        return res

    if not args.all:
        show(f"level={args.level} colour={args.colour}", count_chu(args.level, args.colour, **kw))
        return
    print("Candidate boards, Black to move (canonical conventions: README.md)")
    show("naive (material only)", count_chu("naive"))
    show("+ I1-I3 (file, order, pawn ranks)", count_chu("I3"))
    show("+ I4 (promoted-pawn capacity)", count_chu("I4"))
    c5 = show("+ I5 (brief's capacities) = brief's C", count_chu("I5", stats=True, dist=True))
    cf = show("file-exact (I1-I4, sharpened I5)", count_chu("file"))
    cc = show("file-exact + I6/I7 (bishop, kirin colour)", count_chu("file", colour=True))
    print()
    print("Statistics of the brief's C (level I5):")
    tot = c5.total
    mode = max(c5.by_pieces, key=c5.by_pieces.get)
    pawns = sum((a + b) * v for (a, b), v in c5.by_pawns.items())
    print(f"  mean pieces {c5.mean_pieces:.2f} (mode {mode}); mean unpromoted pawns {pawns / tot:.2f}")
    for t in (8, 10, 12):
        v = sum(v for (a, b), v in c5.by_pawns.items() if max(a, b) >= t)
        print(f"  P(one side has >= {t:2d} unpromoted pawns) = {v / tot:.3e}")
    for t in (10, 12, 14):
        v = sum(v for (a, b), v in c5.by_pawns.items() if a + b >= t)
        print(f"  P(>= {t:2d} unpromoted pawns in total)     = {v / tot:.3e}")
    print()
    print("Canonical conventions: merged roles, royal-capture terminal boards counted")
    prim = show("PRIMARY: file-exact + I6/I7, +e=k, terminals in", count_chu("file", colour=True, **PRIMARY))
    nonterm = show("  of which non-terminal (Black has a royal)", count_chu("file", colour=True, identify_royals=True))
    print(f"  terminal share (Black to move, no Black royal)  {1 - nonterm.total / prim.total:.5f}")
    for c, who in (("W", "White"), ("B", "Black")):
        lone = count(chu_setup("file", lone=c, **PRIMARY), "file", colour=True).total
        print(f"  share with a lone {who} royal (bare-king bound)  {lone / prim.total:.3e}")
    lit = show("SECONDARY: all 39 roles distinct (SFEN-literal)", count(chu_literal_setup(), "file", colour=True))
    print(f"  ratio secondary / primary                     {lit.total / prim.total:.4f}")
    if args.exact:
        print(f"  primary   = {prim.total}")
        print(f"  secondary = {lit.total}")


if __name__ == "__main__":
    main()
