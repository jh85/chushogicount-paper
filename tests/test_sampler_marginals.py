#!/usr/bin/env python3
"""Sampler marginals vs the counter's exact marginals (chu shogi, primary set).

Draws N samples and compares, by chi-square tests with the counter's exact
probabilities (bins with expected count < 5 are pooled):
  * number of pieces on the board;
  * unpromoted pawns per side (joint);
  * terminal (no Black royal) vs not;
  * the U-configuration of a lance file (a) and of a plain file (b), exact
    marginals from the counter with that file's admissible set restricted.

Usage: python3 tests/test_sampler_marginals.py [--n 100000] [--seed 21]
Takes about 5 minutes for 10^5 samples.
"""
import argparse
import math
import random
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))
from count import candidates as cd                           # noqa: E402
from count.candidates import PRIMARY, chu_setup, count       # noqa: E402
from count.sampler import Sampler                            # noqa: E402


def chi2_report(name, observed, expected_prob, n):
    """Pool bins with expected < 5; return (chi2, df, z)."""
    items = sorted(expected_prob)
    chi2, df, pooled_o, pooled_e = 0.0, 0, 0, 0.0
    for k in items:
        e, o = expected_prob[k] * n, observed.get(k, 0)
        if e < 5:
            pooled_o += o
            pooled_e += e
            continue
        chi2 += (o - e) ** 2 / e
        df += 1
    unexpected = sum(v for k, v in observed.items() if k not in expected_prob)
    pooled_o += unexpected
    if pooled_e > 0:
        chi2 += (pooled_o - pooled_e) ** 2 / pooled_e
        df += 1
    df -= 1
    z = (chi2 - df) / math.sqrt(2 * df) if df > 0 else 0.0
    print(f"  {name:28s} chi2 {chi2:8.1f}  df {df:4d}  z {z:+.2f}  (unexpected values: {unexpected})")
    return z


def file_marginal(setup, x, level, colour, total):
    """Exact P(feature key of file x) via a restricted admissible set, plus the
    configs per key (the counter treats configs with equal features alike).
    Returns ({key: prob}, {config: key})."""
    slots = tuple(setup.files[x])
    full = cd._admissible(slots, setup.nranks, setup.zone)
    bykey = {}
    for u, fam in full.items():
        f = cd.file_features(setup, x, u, level, colour)
        key = f[:7] + tuple(sorted(f[7].items()))
        bykey.setdefault(key, {})[u] = fam
    probs, config_key = {}, {}
    orig_table = cd._file_table

    def restricted_table(cfgs):
        def table(setup_, x_, level_, colour_, stats_, etypes_):
            if x_ != x:
                return orig_table(setup_, x_, level_, colour_, stats_, etypes_)
            out = Counter()
            for u in cfgs:
                upb, upw, cb, cw, j, d0, d1, elig = cd.file_features(setup_, x_, u, level_, colour_)
                if not stats_:
                    upb = upw = 0
                out[(upb, upw, cb, cw, j, d0, d1) + tuple(elig.get(t, 0) for t in etypes_)] += 1
            return out
        return table

    for key, cfgs in bykey.items():
        cd._file_table = restricted_table(cfgs)
        try:
            probs[key] = count(setup, level, colour).total / total
        finally:
            cd._file_table = orig_table
        for u in cfgs:
            config_key[u] = key
    return probs, config_key


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=100000)
    ap.add_argument("--seed", type=int, default=21)
    args = ap.parse_args()
    setup = chu_setup("file", **PRIMARY)
    exact = count(setup, "file", colour=True, stats=True, dist=True)
    total = exact.total
    s = Sampler(setup, "file", True)
    assert s.total == total
    rng = random.Random(args.seed)
    pieces, pawns, term, file_a, file_b = Counter(), Counter(), Counter(), Counter(), Counter()
    for _ in range(args.n):
        board, info = s.sample(rng)
        pieces[len(board)] += 1
        up = Counter(p for p in board.values() if p[1] == "P")
        pawns[(up[("B", "P")], up[("W", "P")])] += 1
        term[not any(p == ("B", "K") for p in board.values())] += 1
        for x, c in ((0, file_a), (1, file_b)):
            u = tuple(next((r for r in range(1, 13) if board.get((x, r)) == (sl.colour, sl.kind)), 0)
                      for sl in setup.files[x])
            c[u] += 1
    n = args.n
    print(f"{n} samples, seed {args.seed}; z = (chi2 - df)/sqrt(2 df), |z| < 4 expected")
    zs = [chi2_report("pieces on board", pieces, {k: v / total for k, v in exact.by_pieces.items()}, n),
          chi2_report("unpromoted pawns (B, W)", pawns, {k: v / total for k, v in exact.by_pawns.items()}, n)]
    req = count(chu_setup("file", identify_royals=True), "file", colour=True).total
    zs.append(chi2_report("terminal vs not", term, {False: req / total, True: 1 - req / total}, n))
    for x, c, name in ((1, file_b, "file b (plain)"), (0, file_a, "file a (lance)")):
        probs, config_key = file_marginal(setup, x, "file", True, total)
        by_key = Counter()
        for u, v in c.items():
            by_key[config_key[u]] += v
        zs.append(chi2_report(name + " feature key", by_key, probs, n))
        # uniformity within keys: pool all configs of all keys with expected >= 5
        chi2, df = 0.0, 0
        for key, m in by_key.items():
            cfgs = [u for u, k in config_key.items() if k == key]
            e = m / len(cfgs)
            if e < 5 or len(cfgs) < 2:
                continue
            chi2 += sum((c.get(u, 0) - e) ** 2 / e for u in cfgs)
            df += len(cfgs) - 1
        z = (chi2 - df) / math.sqrt(2 * df) if df else 0.0
        print(f"  {name + ' within-key uniform':28s} chi2 {chi2:8.1f}  df {df:4d}  z {z:+.2f}")
        zs.append(z)
    assert all(abs(z) < 4 for z in zs), zs
    print("ok")


if __name__ == "__main__":
    main()
