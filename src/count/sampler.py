#!/usr/bin/env python3
"""Uniform sampling of candidate boards (the set counted by candidates.py).

Decomposition, top-down (every step is an exact weighted choice with big ints):
  1. the summary key T of the confined pieces of all files:
       (cb, cw, j, d0, d1, caps per promoted type), with weight
       S_0[T] * completions(T);
  2. per file, a feature key consistent with T (prefix/suffix convolution
     tables), then a uniform U-configuration with that key;
  3. the number k of promoted confined pieces, then its split into tokins and
     the other types; 4. the free-piece tag (colour-constrained counts) and the
     number j of free pieces, then the per-group states; 5. squares.

Sampler(setup, level, colour).total must equal candidates.count(...).total; this
and a chi-square test on small boards are in tests/test_sampler.py.

Usage: python3 src/count/sampler.py [--n N] [--seed S]   (prints sample SFENs)
"""
import argparse
import random
import sys
from bisect import bisect_right
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import accumulate
from math import comb, factorial
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.candidates import (PRIMARY, Setup, _admissible, _free_polys, chu_setup,  # noqa: E402
                              elig_types, file_features, is_candidate, sq_class)
from count import filegame                                                       # noqa: E402


def weighted_choice(rng, items, weights):
    cum = list(accumulate(weights))
    assert cum[-1] > 0
    return items[bisect_right(cum, rng.randrange(cum[-1]))]


def falling(n, k):
    r = 1
    for i in range(k):
        r *= n - i
    return r


class Sampler:
    def __init__(self, setup, level="file", colour=True):
        self.setup, self.level, self.colour = setup, level, colour
        self.etypes = elig_types(setup)
        self.nslots = defaultdict(int)
        for f in setup.files:
            for s in f:
                self.nslots[(s.colour, s.kind)] += 1
        if colour:
            self.cap0 = sum((x + r) % 2 == 0 for x in range(setup.nfiles) for r in range(1, setup.nranks + 1))
            self.cap1 = setup.nsquares - self.cap0
        else:
            self.cap0, self.cap1 = setup.nsquares, 0
        # keys (cb, cw, j, d0, d1, caps...) are packed into one int (mixed radix)
        # so that convolution is integer addition
        self.radix = [16, 16, 16, 64, 64] + [4] * len(self.etypes)
        # per-file tables: packed feature key -> list of U-configs.  File order for
        # sampling: the two biggest tables (lance files) first and last, so that
        # the suffix tables stay small.
        tabs = {}
        for x, slots in enumerate(setup.files):
            tab = defaultdict(list)
            for u in _admissible(tuple(slots), setup.nranks, setup.zone):
                _, _, cb, cw, j, d0, d1, elig = file_features(setup, x, u, level, colour)
                tab[self.pack((cb, cw, j, d0, d1) + tuple(elig.get(t, 0) for t in self.etypes))].append(u)
            tabs[x] = dict(tab)
        self.order = sorted(range(setup.nfiles), key=lambda x: len(tabs[x]))
        if len(self.order) > 1:
            self.order = [self.order[-1]] + self.order[:-1]
        self.file_tables = [tabs[x] for x in self.order]
        nf = setup.nfiles
        self.suffix = [None] * (nf + 1)
        self.suffix[nf] = {0: 1}
        for f in range(nf - 1, -1, -1):
            out = defaultdict(int)
            for ka, va in self.file_tables[f].items():
                n = len(va)
                for kb, vb in self.suffix[f + 1].items():
                    out[ka + kb] += n * vb
            self.suffix[f] = dict(out)
        self.free = _free_polys(setup, colour)
        self.keys = [self.unpack(k) for k in self.suffix[0]]
        self.kmax = max(k[2] for k in self.keys) + sum(self.nslots[t] for t in self.etypes) + 1
        # weights of the summary keys
        self.weights = [w * self.completions(T) for T, w in zip(self.keys, self.suffix[0].values())]
        self.total = sum(self.weights)
        self.cum = list(accumulate(self.weights))

    def pack(self, key):
        v = 0
        for r, c in zip(self.radix, key):
            assert 0 <= c < r
            v = v * r + c
        return v

    def unpack(self, v):
        out = []
        for r in reversed(self.radix):
            v, c = divmod(v, r)
            out.append(c)
        return tuple(reversed(out))

    # --- weights ---------------------------------------------------------------
    @lru_cache(maxsize=None)
    def tok(self, cb, cw, j):
        return [sum(comb(t, tb) for tb in range(t + 1) if tb <= cb and t - tb <= cw) for t in range(j + 1)]

    @lru_cache(maxsize=None)
    def cap_terms(self, caps):
        """[(count vector, weight)] for the non-pawn promoted confined pieces;
        weight = r! / prod(i!)  (labelled, scaled so that everything is an int)."""
        vecs = [()]
        for cap in caps:
            vecs = [v + (i,) for v in vecs for i in range(cap + 1)]
        out = defaultdict(list)
        for v in vecs:
            r = sum(v)
            w = factorial(r)
            for i in v:
                w //= factorial(i)
            out[r].append((v, w))
        return dict(out)

    def vec(self, T):
        return self._vec(T[:3] + T[5:])

    @lru_cache(maxsize=None)
    def _vec(self, key):
        """vec[k] = labelled number of type assignments for k promoted confined pieces."""
        cb, cw, j = key[:3]
        ct = self.cap_terms(key[3:])
        cpoly = [sum(w for _, w in ct.get(r, [])) for r in range(max(ct) + 1)]
        out = [0] * self.kmax
        for t, tv in enumerate(self.tok(cb, cw, j)):
            for r, cv in enumerate(cpoly):
                out[t + r] += tv * cv * comb(t + r, t)
        return out

    @lru_cache(maxsize=None)
    def free_terms(self, d0, d1, k):
        """[(tag, j, weight)]: colour-constrained counts tag, j free pieces."""
        f0, f1 = self.cap0 - d0, self.cap1 - d1
        out = []
        for (a0, a1), g in self.free.items():
            ways = falling(f0, a0) * falling(f1, a1)
            fp = f0 + f1 - a0 - a1
            for j, gj in enumerate(g):
                w = ways * gj * comb(k + j, j) * comb(fp, k + j)
                if w:
                    out.append(((a0, a1), j, w))
        return out

    @lru_cache(maxsize=None)
    def _h(self, tag, n):
        return sum(gj * comb(n, j) for j, gj in enumerate(self.free[tag]))

    @lru_cache(maxsize=None)
    def uu(self, d0, d1):
        """uu[k] = sum of free_terms weights; C(k+j,j) C(fp,k+j) = C(fp,k) C(fp-k,j)."""
        f0, f1 = self.cap0 - d0, self.cap1 - d1
        out = [0] * self.kmax
        for (a0, a1) in self.free:
            ways = falling(f0, a0) * falling(f1, a1)
            fp = f0 + f1 - a0 - a1
            if ways:
                for k in range(min(self.kmax, fp + 1)):
                    out[k] += ways * comb(fp, k) * self._h((a0, a1), fp - k)
        return out

    def completions(self, T):
        vec, uu = self.vec(T), self.uu(T[3], T[4])
        return sum(v * u for v, u in zip(vec, uu) if v)

    # --- free-piece groups: suffix EGF products per tag --------------------------
    @lru_cache(maxsize=None)
    def group_list(self):
        return [(c, g) for c in "BW" for g in self.setup.free[c]]

    @lru_cache(maxsize=None)
    def group_suffix(self, i):
        """{(a0, a1): [EGF coefficient per m]} of groups i.. combined."""
        if i == len(self.group_list()):
            return {(0, 0): [Fraction(1)]}
        nxt = self.group_suffix(i + 1)
        out = {}
        for m, div, a0, a1 in self.group_list()[i][1].terms(self.colour):
            for (b0, b1), lst in nxt.items():
                tgt = out.setdefault((a0 + b0, a1 + b1), [])
                tgt.extend([Fraction(0)] * (m + len(lst) - len(tgt)))
                for mm, v in enumerate(lst):
                    tgt[m + mm] += v / div
        return out

    # --- sampling ---------------------------------------------------------------
    def sample(self, rng):
        """One uniform candidate: (board dict, info dict)."""
        T = self.keys[bisect_right(self.cum, rng.randrange(self.total))]
        # files
        board, rest = {}, self.pack(T)
        for f, tab in enumerate(self.file_tables):
            x = self.order[f]
            items, weights = [], []
            for k, configs in tab.items():
                remain = rest - k
                if remain >= 0 and all(a <= b for a, b in zip(self.unpack(k), self.unpack(rest))):
                    w = self.suffix[f + 1].get(remain, 0) * len(configs)
                    if w:
                        items.append(k)
                        weights.append(w)
            k = weighted_choice(rng, items, weights)
            u = rng.choice(tab[k])
            for slot, r in zip(self.setup.files[x], u):
                if r:
                    board[(x, r)] = (slot.colour, slot.kind)
            rest -= k
        assert rest == 0
        cb, cw, j, d0, d1 = T[:5]
        # promoted confined: k total, then t tokins and r others
        vec, uu = self.vec(T), self.uu(d0, d1)
        k = weighted_choice(rng, list(range(self.kmax)), [v * u for v, u in zip(vec, uu)])
        tokp, ct = self.tok(cb, cw, j), self.cap_terms(T[5:])
        pairs = [(t, k - t) for t in range(len(tokp)) if k - t in ct]
        t, r = weighted_choice(rng, pairs, [tokp[t] * comb(k, t) * sum(w for _, w in ct[r]) for t, r in pairs])
        tb = weighted_choice(rng, list(range(t + 1)), [comb(t, x) if x <= cb and t - x <= cw else 0 for x in range(t + 1)])
        cv = weighted_choice(rng, [v for v, _ in ct[r]], [w for _, w in ct[r]])
        pieces = [("B", "+P")] * tb + [("W", "+P")] * (t - tb)
        for (c, kind), n in zip(self.etypes, cv):
            pieces += [(c, "+" + kind)] * n
        # free pieces
        ft = self.free_terms(d0, d1, k)
        tag, jj, _ = weighted_choice(rng, ft, [w for _, _, w in ft])
        constrained = {0: [], 1: []}
        a0, a1, m_left = tag[0], tag[1], jj
        for i, (c, g) in enumerate(self.group_list()):
            nxt = self.group_suffix(i + 1)
            opts, ws = [], []
            for st in g.states(self.colour):
                m, div, x0, x1 = st[:4]
                lst = nxt.get((a0 - x0, a1 - x1))
                if lst and m <= m_left and m_left - m < len(lst) and lst[m_left - m]:
                    opts.append(st)
                    ws.append(lst[m_left - m] / div)
            st = weighted_choice(rng, opts, _integerize(ws))
            m, div, x0, x1, free_pieces, bound = st
            a0, a1, m_left = a0 - x0, a1 - x1, m_left - m
            pieces += [(c, role) for role in free_pieces]
            for cls in (0, 1):
                constrained[cls] += [(c, role) for role in bound[cls]]
        assert (a0, a1, m_left) == (0, 0, 0)
        # squares
        empty = [s for x in range(self.setup.nfiles) for r in range(1, self.setup.nranks + 1)
                 if (s := (x, r)) not in board]
        rng.shuffle(empty)
        by_class = {0: [s for s in empty if sq_class(s) == 0], 1: [s for s in empty if sq_class(s) == 1]}
        for cls in (0, 1):
            for piece in constrained[cls]:
                board[by_class[cls].pop()] = piece
        free_sq = by_class[0] + by_class[1]
        rng.shuffle(free_sq)
        rng.shuffle(pieces)
        for piece, s in zip(pieces, free_sq):
            board[s] = piece
        return board, {"T": T, "k": k, "j": jj, "tag": tag}


def _gcd(a, b):
    while b:
        a, b = b, a % b
    return a


def _integerize(ws):
    """Fractions with a common denominator -> proportional ints."""
    scale = 1
    for w in ws:
        scale = scale * w.denominator // _gcd(scale, w.denominator)
    return [int(w * scale) for w in ws]


def to_sfen(board, turn="b", flag="-"):
    """Board dict -> lishogi SFEN (merged roles written as n, q, k)."""
    from count.sfen import BASE
    inv = {v: k for k, v in BASE.items()}
    rows = []
    for r in range(12, 0, -1):
        row, empty = "", 0
        for x in range(12):
            p = board.get((x, r))
            if p is None:
                empty += 1
                continue
            if empty:
                row += str(empty)
                empty = 0
            c, role = p
            letter = ("+" if role.startswith("+") else "") + inv[role.lstrip("+")]
            row += letter.upper() if c == "B" else letter
        if empty:
            row += str(empty)
        rows.append(row)
    return "/".join(rows) + f" {turn} {flag} 1"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--n", type=int, default=5)
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args()
    s = Sampler(chu_setup("file", **PRIMARY), "file", True)
    rng = random.Random(args.seed)
    for i in range(args.n):
        board, info = s.sample(rng)
        assert is_candidate(s.setup, board, "file", True)
        print(to_sfen(board))


if __name__ == "__main__":
    main()


# ---------------------------------------------------------------------------
# Ranking: the inverse of the counting decomposition (a perfect hash of the
# candidate set, used by the validation BFS as a bitset index).
# ---------------------------------------------------------------------------
def rank_subset(chosen, n):
    """Lexicographic rank of a sorted k-subset of range(n)."""
    k, r, prev = len(chosen), 0, -1
    for i, s in enumerate(chosen):
        for v in range(prev + 1, s):
            r += comb(n - 1 - v, k - 1 - i)
        prev = s
    return r


def rank_multiset_perm(seq, key=None):
    """Lexicographic rank of seq among the distinct permutations of its multiset."""
    from collections import Counter
    key = key or (lambda x: x)
    cnt = Counter(seq)
    n, r = len(seq), 0
    for i, x in enumerate(seq):
        for y in sorted(cnt, key=key):
            if key(y) >= key(x):
                break
            if cnt[y]:
                cnt[y] -= 1
                m = n - i - 1
                ways = factorial(m)
                for v in cnt.values():
                    ways //= factorial(v)
                r += ways
                cnt[y] += 1
        cnt[x] -= 1
    return r


class Ranker:
    """rank(board) in [0, sampler.total): a bijection onto the candidate set
    counted by the sampler's decomposition (same Setup, level, colour)."""

    def __init__(self, sampler):
        self.s = sampler
        self.setup = sampler.setup
        self.key_index = {k: i for i, k in enumerate(sampler.keys)}
        self.cum_before = [0] + sampler.cum[:-1]
        self.conf_kinds = {s.kind for f in self.setup.files for s in f}
        self.groups = sampler.group_list()

    def rank(self, board):
        s, setup = self.s, self.setup
        # --- confined U pieces: per-file configs and feature keys -------------
        file_keys, file_cfgs = [], []
        for x, slots in enumerate(setup.files):
            idx = {(sl.colour, sl.kind): i for i, sl in enumerate(slots)}
            u = [0] * len(slots)
            for r in range(1, setup.nranks + 1):
                p = board.get((x, r))
                if p and p[1] in self.conf_kinds and p in idx:
                    u[idx[p]] = r
            u = tuple(u)
            _, _, cb, cw, j, d0, d1, elig = file_features(setup, x, u, s.level, s.colour)
            k = s.pack((cb, cw, j, d0, d1) + tuple(elig.get(t, 0) for t in s.etypes))
            file_keys.append(k)
            file_cfgs.append(u)
        T_packed = sum(file_keys)
        T = s.unpack(T_packed)
        base = self.cum_before[self.key_index[T]]
        # rank of the file-config combination (mixed radix in sampling order)
        rank_files, rest = 0, T_packed
        for f, tab in enumerate(s.file_tables):
            x = s.order[f]
            k, cfg = file_keys[x], file_cfgs[x]
            for k2, cfgs in tab.items():
                if k2 == k:
                    break
                remain = rest - k2
                if remain >= 0 and all(a <= b for a, b in zip(s.unpack(k2), s.unpack(rest))):
                    rank_files += s.suffix[f + 1].get(remain, 0) * len(cfgs)
            rank_files += tab[k].index(cfg) * s.suffix[f + 1][rest - k]
            rest -= k
        comp = s.completions(T)
        return base + rank_files * comp + self.rank_completion(board, T)

    def rank_completion(self, board, T):
        s, setup = self.s, self.setup
        cb, cw, jtok, d0, d1 = T[:5]
        confined_u = {sq for sq, p in board.items() if p[1] in self.conf_kinds and not p[1].startswith("+")}
        # promoted confined pieces (sorted by square) and free pieces
        prom_conf = sorted((sq, p) for sq, p in board.items()
                           if p[1].startswith("+") and p[1][1:] in self.conf_kinds)
        free = sorted((sq, p) for sq, p in board.items() if sq not in confined_u and (sq, p) not in prom_conf)
        k = len(prom_conf)
        vec, uu = s.vec(T), s.uu(d0, d1)
        r_total = sum(v * u for v, u in zip(vec[:k], uu[:k]))
        # --- type sequence on the k promoted-confined squares --------------------
        types = [p for _, p in prom_conf]
        t = sum(1 for p in types if p[1] == "+P")
        rr = k - t
        tokp, ct = s.tok(cb, cw, jtok), s.cap_terms(T[5:])
        pairs = [(t_, k - t_) for t_ in range(len(tokp)) if k - t_ in ct]
        rank_vec = 0
        for (t2, r2) in pairs:
            if (t2, r2) == (t, rr):
                break
            rank_vec += tokp[t2] * comb(k, t2) * sum(w for _, w in ct[r2])
        tok_pos = [i for i, p in enumerate(types) if p[1] == "+P"]
        r_pos = rank_subset(tok_pos, k)
        tb_seq = [p[0] for p in types if p[1] == "+P"]
        tb = tb_seq.count("B")
        r_tok = sum(comb(t, x) for x in range(tb) if x <= cb and t - x <= cw) + \
            rank_subset([i for i, c in enumerate(tb_seq) if c == "B"], t)
        others = [p for p in types if p[1] != "+P"]
        cv = tuple(sum(1 for p in others if p == (c, "+" + kind)) for (c, kind) in s.etypes)
        r_cap = 0
        for v, w in ct[rr]:
            if v == cv:
                break
            r_cap += w
        order = {(c, "+" + kind): i for i, (c, kind) in enumerate(s.etypes)}
        r_cap += rank_multiset_perm(others, key=lambda p: order[p])
        rank_vec += (r_pos * tokp[t] + r_tok) * sum(w for _, w in ct[rr]) + r_cap
        # --- free pieces: tag, j, constrained squares, free squares, sequence -----
        states = self.group_states(free)          # per group: chosen state tuple
        a0 = sum(st[2] for st in states)
        a1 = sum(st[3] for st in states)
        bound = {0: [], 1: []}
        for (c, g), st in zip(self.groups, states):
            for cls in (0, 1):
                bound[cls] += [(c, role) for role in st[5][cls]]
        free_pieces = [(sq, p) for sq, p in free]
        unconstrained = list(free_pieces)
        placed_bound = {0: [], 1: []}
        for cls in (0, 1):
            for piece in bound[cls]:
                sq = next(sq for sq, p in unconstrained if p == piece and sq_class(sq) == cls)
                unconstrained.remove((sq, piece))
                placed_bound[cls].append(sq)
        j = len(unconstrained)
        ft = s.free_terms(d0, d1, k)
        rank_uu = 0
        for tag, jj, w in ft:
            if (tag, jj) == ((a0, a1), j):
                break
            rank_uu += w
        f0 = [sq for sq in SQUARES_OF(setup) if sq not in confined_u and sq_class(sq) == 0] if s.colour else \
             [sq for sq in SQUARES_OF(setup) if sq not in confined_u]
        f1 = [sq for sq in SQUARES_OF(setup) if sq not in confined_u and sq_class(sq) == 1] if s.colour else []
        # constrained placements: ordered (class 0 pieces first, then class 1), falling factorial
        r_con, avail0, avail1 = 0, list(f0), list(f1)
        for cls, avail in ((0, avail0), (1, avail1)):
            for sq in placed_bound[cls]:
                i = avail.index(sq)
                r_con = r_con * len(avail) + i
                avail.pop(i)
        n_con_ways = falling(len(f0), a0) * falling(len(f1), a1)
        remaining = sorted(avail0 + avail1)
        g = s.free[(a0, a1)]
        fp = len(remaining)
        block = g[j] * comb(k + j, j) * comb(fp, k + j)
        # squares of the k + j pieces among the remaining squares, then the split
        kj_squares = sorted([sq for sq, _ in prom_conf] + [sq for sq, _ in unconstrained])
        pos = {sq: i for i, sq in enumerate(remaining)}
        r_sq = rank_subset([pos[sq] for sq in kj_squares], fp)
        free_pos = [i for i, sq in enumerate(kj_squares) if sq in {q for q, _ in unconstrained}]
        r_split = rank_subset(free_pos, k + j)
        r_seq = self.rank_free_sequence([p for _, p in sorted(unconstrained)], states, (a0, a1), j)
        rank_rest = (r_sq * comb(k + j, j) + r_split) * g[j] + r_seq
        rank_uu += r_con * block + rank_rest
        return r_total + rank_vec * uu[k] + rank_uu

    def group_states(self, free):
        """The state of every group given the free pieces on the board."""
        from collections import Counter
        cnt = Counter(p for _, p in free)
        bycls = {0: Counter(p for sq, p in free if sq_class(sq) == 0),
                 1: Counter(p for sq, p in free if sq_class(sq) == 1)}
        states = []
        for c, g in self.groups:
            for st in g.states(self.s.colour):
                have = Counter(st[4]) + Counter(st[5][0]) + Counter(st[5][1])
                if not all(have[r] == cnt[(c, r)] for r in g.roles()):
                    continue
                # bound pieces must sit on their class (a role bound in one state
                # is never free in another state of the same group)
                if all(Counter(st[5][cls])[r] <= bycls[cls][(c, r)] for cls in (0, 1) for r in set(st[5][cls])):
                    states.append(st)
                    break
            else:
                raise ValueError(f"no state of {g} matches {dict(cnt)}")
        return states

    def rank_free_sequence(self, seq, states, tag, j):
        """Rank of the sequence of unconstrained free pieces (by square) among
        the G'[tag][j] labelled sequences: state combinations in sampling order,
        then multiset permutations in lexicographic order."""
        s = self.s
        r = Fraction(0)
        a0, a1, m_left = tag[0], tag[1], j
        prefix_inv = Fraction(1)
        for i, ((c, g), chosen) in enumerate(zip(self.groups, states)):
            nxt = s.group_suffix(i + 1)
            for st in g.states(s.colour):
                if st == chosen:
                    break
                m, div, x0, x1 = st[:4]
                lst = nxt.get((a0 - x0, a1 - x1))
                if lst and m <= m_left and m_left - m < len(lst) and lst[m_left - m]:
                    r += factorial(j) * prefix_inv * Fraction(1, div) * lst[m_left - m]
            m, div, x0, x1 = chosen[:4]
            prefix_inv /= div
            a0, a1, m_left = a0 - x0, a1 - x1, m_left - m
        assert r.denominator == 1
        order = {}
        for gi, (c, g) in enumerate(self.groups):
            for ri, role in enumerate(g.roles()):
                order[(c, role)] = (gi, ri)
        return int(r) + rank_multiset_perm(seq, key=lambda p: order[p])


def SQUARES_OF(setup):
    return [(x, r) for x in range(setup.nfiles) for r in range(1, setup.nranks + 1)]
