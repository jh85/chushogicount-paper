#!/usr/bin/env python3
"""Independent exact count of the candidate set C (Black to move) and of its terminal
and lone-royal subsets (cross-check of candidates.py, 2026-10-16).  Shares no code with
src/count: inventory, files and colour classes are read from the initial SFEN; the
per-file game (Theorem F of docs/invariants.md) is re-implemented.

Usage: python3 src/count/independent.py OUT.json [--dup]    (about 7 min per mode)

Set definition reproduced (docs/invariants.md §6, candidates.py semantics):
  I1-I3  unpromoted P/L/RC/GB: per file, a state of the abstract file game
  I4     promoted pawns: TB <= sum cb, TW <= sum cw, TB+TW <= sum j (per-file caps)
  I5'    promoted L/RC/GB of colour c, type t: <= number of slots of (c,t) that are
         off the board and can be promoted alone in the file game with that U-config
  I6/I7  unpromoted bishops: per colour class <= start count; unpromoted kirin on its class
  I8     White has a royal; Black may have none (terminal)
  I9     per base type <= initial number; D2: +o = n, +x = q, +e = k (crown prince = K)
Royal states per side under D2, as (K, E): (0,0) (0,1) (1,0) (1,1) (2,0).
`dup=True` gives (1,0) weight 2, as candidates.Royal.states(identify=True) did before
the fix of 2026-10-16 (reproduces the old counts.md integers).

Bare-king sets: lone_X = side X is a single royal and nothing else; lone_X+dead = a
single royal plus any unpromoted pawns / lances on their last rank (dead pieces, which
lishogi's bare-king and insufficient-material rules ignore); C_t_B_dead_only = terminal
boards on which Black has nothing but dead pieces.
"""
import sys
from fractions import Fraction
from math import factorial, comb
from functools import lru_cache
from collections import defaultdict

START = "lfcsgekgscfl/a1b1txot1b1a/mvrhdqndhrvm/pppppppppppp/3i4i3/12/12/3I4I3/PPPPPPPPPPPP/MVRHDNQDHRVM/A1B1TOXT1B1A/LFCSGKEGSCFL"
NF = NR = 12
ZONE = 4
CONFINED = {"p": "P", "l": "L", "a": "RC", "i": "GB"}

# ---- read the initial position -------------------------------------------------
pieces = []                                  # (colour, letter, x, r); x=0 is SFEN's left (file 12), r=1 Black's back rank
for row_i, row in enumerate(START.split("/")):
    r = NR - row_i
    x = 0
    num = ""
    for ch in row:
        if ch.isdigit():
            num += ch
            continue
        if num:
            x += int(num); num = ""
        pieces.append(("B" if ch.isupper() else "W", ch.lower(), x, r))
        x += 1
    if num:
        x += int(num)
    assert x == NF
cls = lambda x, r: (x + r) % 2

inv = {c: defaultdict(int) for c in "BW"}
for c, l, x, r in pieces:
    inv[c][l] += 1
assert inv["B"] == inv["W"]
INV = dict(inv["B"])
assert INV == {'l': 2, 'f': 2, 'c': 2, 's': 2, 'g': 2, 'e': 1, 'k': 1, 'a': 2, 'b': 2, 't': 2,
               'x': 1, 'o': 1, 'm': 2, 'v': 2, 'r': 2, 'h': 2, 'd': 2, 'q': 1, 'n': 1, 'p': 12, 'i': 2}
bishop_classes = {c: sorted(cls(x, r) for cc, l, x, r in pieces if cc == c and l == "b") for c in "BW"}
kirin_class = {c: [cls(x, r) for cc, l, x, r in pieces if cc == c and l == "o"][0] for c in "BW"}
assert bishop_classes == {"B": [0, 1], "W": [0, 1]} and kirin_class == {"B": 1, "W": 1}

# file slots: (colour, kind, start rank), per file
file_slots = [[] for _ in range(NF)]
for c, l, x, r in pieces:
    if l in CONFINED:
        file_slots[x].append((c, CONFINED[l], r))
for s in file_slots:
    s.sort(key=lambda t: t[2])

# ---- abstract file game ----------------------------------------------------------
GONE, PROM = 0, -1


def zone(c, r):
    return r > NR - ZONE if c == "B" else r <= ZONE


def file_states(slots):
    start = tuple(s[2] for s in slots)
    seen = {start}
    todo = [start]
    while todo:
        st = todo.pop()
        occ = {r for r in st if r > 0}
        for i, r in enumerate(st):
            if r <= 0:
                continue
            c, kind, _ = slots[i]
            fwd = 1 if c == "B" else -1
            dirs = {"P": [fwd], "L": [fwd], "GB": [fwd, -fwd], "RC": [fwd, -fwd]}[kind]
            slide = kind in ("L", "RC")
            nxt = [st[:i] + (GONE,) + st[i + 1:]]
            for d in dirs:
                b = r + d
                while 1 <= b <= NR and b not in occ:
                    nxt.append(st[:i] + (b,) + st[i + 1:])
                    if zone(c, r) or zone(c, b):
                        nxt.append(st[:i] + (PROM,) + st[i + 1:])
                    if not slide:
                        break
                    b += d
            for t in nxt:
                if t not in seen:
                    seen.add(t); todo.append(t)
    fam = defaultdict(set)
    for st in seen:
        fam[tuple(max(r, 0) for r in st)].add(frozenset(i for i, r in enumerate(st) if r == PROM))
    return fam


CAPTYPES = [(c, k) for c in "BW" for k in ("L", "RC", "GB")]


def file_table(x, lone="", dead_ok=False):
    """[(d0, d1, cb, cw, j, caps tuple over CAPTYPES)] for the admissible U-configs of
    file x.  lone: that colour keeps no unpromoted slot (dead_ok: except a pawn or lance
    on its last rank) and no promoted piece."""
    slots = file_slots[x]
    out = defaultdict(int)
    for u, fam in file_states(slots).items():
        ok = True
        for i, r in enumerate(u):
            c, kind, _ = slots[i]
            if r and c in lone:
                last = NR if c == "B" else 1
                if not (dead_ok and kind in ("P", "L") and r == last):
                    ok = False
        if not ok:
            continue
        d = [0, 0]
        for i, r in enumerate(u):
            if r:
                d[cls(x, r)] += 1
        alone = lambda i: frozenset([i]) in fam
        idx = {(s[0], s[1]): i for i, s in enumerate(slots)}
        cb = int(("B", "P") in idx and alone(idx[("B", "P")]) and "B" not in lone)
        cw = int(("W", "P") in idx and alone(idx[("W", "P")]) and "W" not in lone)
        j = int(cb or cw)
        caps = tuple(int(t in idx and not u[idx[t]] and alone(idx[t]) and t[0] not in lone) for t in CAPTYPES)
        out[(d[0], d[1], cb, cw, j, caps)] += 1
    return out


def egf(maxn):
    return [Fraction(1, factorial(t)) for t in range(maxn + 1)]


def pmul(a, b):
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for k, y in enumerate(b):
                out[i + k] += x * y
    return out


def padd(a, b):
    if len(a) < len(b):
        a, b = b, a
    a = list(a)
    for i, v in enumerate(b):
        a[i] += v
    return a


@lru_cache(maxsize=None)
def confined_part(lone="", dead_ok=False):
    """{(d0, d1, CB, CW, J): EGF polynomial of the promoted L/RC/GB pieces (summed over configs)}.
    Caps are summed per (colour, type) over all files first: promoted pieces of one type
    are identical whichever file they came from (one 1/t! for the type)."""
    acc = {(0, 0, 0, 0, 0) + (0,) * len(CAPTYPES): 1}
    for x in range(NF):
        tab = file_table(x, lone, dead_ok)
        new = defaultdict(int)
        for k1, n1 in acc.items():
            for (d0, d1, cb, cw, j, caps), n2 in tab.items():
                k = tuple(a + b for a, b in zip(k1, (d0, d1, cb, cw, j) + caps))
                new[k] += n1 * n2
        acc = new
    out = defaultdict(lambda: [Fraction(0)])
    for k, n in acc.items():
        p = [Fraction(n)]
        for cap in k[5:]:
            p = pmul(p, egf(cap))
        out[k[:5]] = padd(out[k[:5]], p)
    return out


def pawn_poly(CB, CW, J):
    p = [Fraction(0)] * (J + 1)
    for tb in range(CB + 1):
        for tw in range(CW + 1):
            if tb + tw <= J:
                p[tb + tw] += Fraction(1, factorial(tb) * factorial(tw))
    return p


# ---- free pieces -------------------------------------------------------------------
def side_groups(c, royal, dup, lone):
    """List of groups; a group is a list of states (m_unbound, weight Fraction, a0, a1).
    royal: 'required' | 'optional' | 'none' (Black of a terminal board: no K)."""
    if lone:
        return [[(1, Fraction(1), 0, 0)]]                       # exactly one K
    g = []
    rs = []                                                      # (K, E) states
    for K, E in ((0, 0), (0, 1), (1, 0), (1, 1), (2, 0)):
        if royal == "required" and K == 0:
            continue
        if royal == "none" and K > 0:
            continue
        w = Fraction(2 if (dup and (K, E) == (1, 0)) else 1, factorial(K))
        rs.append((K + E, w, 0, 0))
    g.append(rs)
    for l in "gscftmvrhd":                                       # 2 each, promotable, distinct promoted roles
        n = INV[l]
        g.append([(u + p, Fraction(1, factorial(u) * factorial(p)), 0, 0)
                  for u in range(n + 1) for p in range(n - u + 1)])
    # bishops: unpromoted bound per class (<= start count per class), promoted free
    bc = bishop_classes[c]
    st = []
    for u0 in range(bc.count(0) + 1):
        for u1 in range(bc.count(1) + 1):
            for p in range(INV["b"] - u0 - u1 + 1):
                st.append((p, Fraction(1, factorial(p)), u0, u1))  # u0,u1 <= 1: one bishop per class
    g.append(st)
    # kirin (bound) + lions (incl. promoted kirin): kirin <= 1, kirin + lions <= 2
    kc = kirin_class[c]
    g.append([(big, Fraction(1, factorial(big)), k * (kc == 0), k * (kc == 1))
              for k in (0, 1) for big in range(3 - k)])
    # phoenix + free kings (incl. promoted phoenix): phoenix <= 1, total <= 2, both free
    g.append([(k + big, Fraction(1, factorial(big)), 0, 0) for k in (0, 1) for big in range(3 - k)])
    return g


def free_polys(groups):
    """{(a0, a1): EGF poly over unbound piece count}"""
    acc = {(0, 0): [Fraction(1)]}
    for grp in groups:
        new = defaultdict(lambda: [Fraction(0)])
        for (a0, a1), p in acc.items():
            for m, w, b0, b1 in grp:
                q = [Fraction(0)] * m + [w]
                new[(a0 + b0, a1 + b1)] = padd(new[(a0 + b0, a1 + b1)], pmul(p, q))
        acc = new
    return acc


def falling(n, k):
    if k > n:
        return 0
    r = 1
    for i in range(k):
        r *= n - i
    return r


SQ0 = sum(cls(x, r) == 0 for x in range(NF) for r in range(1, NR + 1))
SQ1 = NF * NR - SQ0


def total(black, white, lone="", dead_ok=False):
    """black/white: (royal mode, lone flag); dup applied inside groups."""
    free = free_polys(black + white)
    conf = confined_part(lone, dead_ok)

    @lru_cache(maxsize=None)
    def U(d0, d1, kmax):
        f0, f1 = SQ0 - d0, SQ1 - d1
        out = [0] * (kmax + 1)
        for (a0, a1), g in free.items():
            wb = falling(f0, a0) * falling(f1, a1)
            if not wb:
                continue
            rest = f0 + f1 - a0 - a1
            for k in range(kmax + 1):
                out[k] += wb * sum(gj * falling(rest, k + j) for j, gj in enumerate(g))
        return tuple(out)

    tot = Fraction(0)
    for (d0, d1, CB, CW, J), cp in conf.items():
        q = pmul(cp, pawn_poly(CB, CW, J))
        u = U(d0, d1, len(q) - 1)
        tot += sum(qk * uk for qk, uk in zip(q, u))
    assert tot.denominator == 1
    return tot.numerator


def run(dup):
    B = lambda mode, lone=False: side_groups("B", mode, dup, lone)
    W = lambda mode, lone=False: side_groups("W", mode, dup, lone)
    out = {}
    out["C_nt"] = total(B("required"), W("required"))
    out["C_t"] = total(B("none"), W("required"))
    for dead in (False, True):
        tag = "+dead" if dead else ""
        out["lone_W" + tag] = total(B("optional"), W("required", True), lone="W", dead_ok=dead)
        out["lone_B" + tag] = total(B("required", True), W("required"), lone="B", dead_ok=dead)
        out["lone_both" + tag] = total(B("required", True), W("required", True), lone="BW", dead_ok=dead)
    out["C_t_B_dead_only"] = total([[(0, Fraction(1), 0, 0)]], W("required"), lone="B", dead_ok=True)
    return out


if __name__ == "__main__":
    import json
    res = {}
    for dup in ((False, True) if "--dup" in sys.argv else (False,)):
        r = run(dup)
        r["C"] = r["C_nt"] + r["C_t"]
        res["dup" if dup else "dedup"] = r
        print("dup" if dup else "dedup", {k: f"{v:.6e}" for k, v in r.items()}, flush=True)
    json.dump({k: {kk: str(vv) for kk, vv in v.items()} for k, v in res.items()}, open(sys.argv[1], "w"), indent=1)
