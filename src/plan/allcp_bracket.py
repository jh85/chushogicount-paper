#!/usr/bin/env python3
"""Finite-sample brackets using only Clopper-Pearson bounds (supplementary; construction proposed
in the second external review of sampling precision, 2026-10-30, §4; formulated after run M-F
and the G13b re-analysis, so not registered).

lishogi, and JCSA move rules with the game ending by royal capture (run M-F):
    |R| = N_nt (1 - s_nt) q1 + N_nt mu p2 + N_t p3
with q1 the reachable fraction of I10-satisfying non-terminal boards, p2 / p3 the reachable
fractions of all candidate flag states / terminal boards (refuted and unresolved samples kept
in the denominators as failures), s the I10 shares (10^7 boards per stratum, seed 173) and
mu = E[k] = sum_j P(k >= j) over j = 1..3 (k <= 3; under the JCSA k <= 1, so only j = 1), each
threshold probability bounded by Clopper-Pearson on the 98,975,310 non-terminal boards of the
10^8 static sample (seed 171).  Upper end: N_nt (1 - s_nt) + N_nt mu + N_t (1 - s_t).

JCSA checkmate ending (D13 with D13a, D13b; runs G13/G13b re-analysed):
    N13 = N_nt (1 - s_nt) q,   q in [CP lower on certified, 1 - CP lower on proven unreachable]
over the n' = 39,957 I10-satisfying boards; full |R| (supplementary): N13 below, and above
N13's upper end + N_nt mu_JCSA + N_t (1 - s_t).

Each end is one-sided at 0.00135, split equally over its own one-sided statements; joint
coverage >= 1 - 0.0027 by the union bound, with no normal approximation and no independence
assumption.  Digit rule: both unrounded ends round half up to the same value.

Usage: python3 src/plan/allcp_bracket.py
"""
import math
import sys
from decimal import Decimal, ROUND_HALF_UP
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.candidates import chu_setup, count       # noqa: E402
from plan.budget import cp_lower                     # noqa: E402
from plan.estimate import FLAG_COUNTS                # noqa: E402

ALPHA_END = 0.00135
N_I10 = 10 ** 7
I10 = {"nonterm": 11887, "term": 12036}              # out/runs/lanes_1e7_seed173.log
N_K = 98975310                                       # out/runs/flags_jcsa_1e8_seed171.log
K_JCSA_1 = 1600168 + 267831 + 34734                  # boards with k_JCSA = 1, same log
# run M-F: (certified, denominator); every M-F certificate also holds under the JCSA
Q1 = (399355, 400000 - 487)
P2 = {"lishogi": (39938, 40000), "JCSA": (39922, 40000)}
P3 = (23965, 24000)
# G13 with G13b's records (src/jcsa/d13_bracket.py): certified, proven unreachable, n'
D13 = (39287, 581 + 21, 39957)


def cp_upper(c, n, tail):
    return 1 - cp_lower(n - c, n, tail)


def rounds(lo, hi, digits):
    q = Decimal(1).scaleb(-(digits - 1))
    r = [Decimal(repr(x / 1e164)).quantize(q, rounding=ROUND_HALF_UP) for x in (lo, hi)]
    return r[0] if r[0] == r[1] else None


def show(name, lo, hi, digits):
    r = rounds(lo, hi, digits)
    lo5, hi5 = math.floor(lo / 1e159) / 1e5, math.ceil(hi / 1e159) / 1e5   # rounded outward
    print(f"{name}: [{lo5:.5f}, {hi5:.5f}] x 10^164 (Black to move, outward), width {(hi - lo) / hi * 100:.3f} %,"
          f" x2 [{2 * lo / 1e164:.4f}, {2 * hi / 1e164:.4f}]; {digits} digits: {f'{r} x 10^164' if r else 'no'}")


def main():
    cn = count(chu_setup("file", identify_royals=True), "file", colour=True).total
    ct = count(chu_setup("file", identify_royals=True, terminal_only=True), "file", colour=True).total
    assert sum(v for k, v in FLAG_COUNTS.items()) == N_K
    thr = {"lishogi": [sum(v for k, v in FLAG_COUNTS.items() if k >= j) for j in (1, 2, 3)],
           "JCSA": [K_JCSA_1]}
    for rules in ("lishogi", "JCSA"):
        nl, nu = 4 + len(thr[rules]), 2 + len(thr[rules])    # statements per end
        dl, du = ALPHA_END / nl, ALPHA_END / nu
        q1, p2, p3 = cp_lower(*Q1, dl), cp_lower(*P2[rules], dl), cp_lower(*P3, dl)
        s_nt_hi = cp_upper(I10["nonterm"], N_I10, dl)
        s_nt_lo, s_t_lo = cp_lower(I10["nonterm"], N_I10, du), cp_lower(I10["term"], N_I10, du)
        mu_lo = sum(cp_lower(c, N_K, dl) for c in thr[rules])
        mu_hi = sum(cp_upper(c, N_K, du) for c in thr[rules])
        lo = cn * (1 - s_nt_hi) * q1 + cn * mu_lo * p2 + ct * p3
        hi = cn * (1 - s_nt_lo) + cn * mu_hi + ct * (1 - s_t_lo)
        print(f"{rules}: {nl} + {nu} statements; q1 >= {q1:.6f}, p2 >= {p2:.6f}, p3 >= {p3:.6f},"
              f" s_nt in [{s_nt_lo:.6f}, {s_nt_hi:.6f}], s_t >= {s_t_lo:.6f}, mu in [{mu_lo:.6f}, {mu_hi:.6f}]")
        show(f"  {rules} |R|", lo, hi, 3)
    cert, unr, n = D13
    d = ALPHA_END / 2                                         # N13: two statements per end
    q_lo, q_hi = cp_lower(cert, n, d), 1 - cp_lower(unr, n, d)
    lo13 = cn * (1 - cp_upper(I10["nonterm"], N_I10, d)) * q_lo
    hi13 = cn * (1 - cp_lower(I10["nonterm"], N_I10, d)) * q_hi
    print(f"D13: q in [{q_lo:.5f}, {q_hi:.5f}]")
    show("  N13", lo13, hi13, 2)
    du = ALPHA_END / 4                                        # full |R| upper end: q, s_nt, mu_JCSA, s_t
    hi_r = (cn * (1 - cp_lower(I10["nonterm"], N_I10, du)) * (1 - cp_lower(unr, n, du))
            + cn * cp_upper(K_JCSA_1, N_K, du) + ct * (1 - cp_lower(I10["term"], N_I10, du)))
    show("  D13 |R| (supplementary)", lo13, hi_r, 2)


if __name__ == "__main__":
    main()
