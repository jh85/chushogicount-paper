#!/usr/bin/env python3
"""Bracket-width table for Milestone B: [lower, cap] with Bonferroni over the
six components (p1, p2, p3, E[k], I10 shares of both strata), one-sided
alpha = 0.00135/6 each; exact Clopper-Pearson lower bounds via the regularized
incomplete beta function.  Usage: python3 src/plan/budget.py [--ek 0.02395]"""
import argparse
import math
from statistics import NormalDist

CNT, CT = 1.951903e164, 2.000556e162


def betacf(a, b, x):
    MAXIT, EPS, FPMIN = 300, 1e-14, 1e-300
    qab, qap, qam = a + b, a + 1, a - 1
    c, d = 1.0, 1 - qab * x / qap
    d = 1 / (d if abs(d) >= FPMIN else FPMIN)
    h = d
    for m in range(1, MAXIT + 1):
        m2 = 2 * m
        aa = m * (b - m) * x / ((qam + m2) * (a + m2))
        d = 1 + aa * d
        d = 1 / (d if abs(d) >= FPMIN else FPMIN)
        c = 1 + aa / c
        c = c if abs(c) >= FPMIN else FPMIN
        h *= d * c
        aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2))
        d = 1 + aa * d
        d = 1 / (d if abs(d) >= FPMIN else FPMIN)
        c = 1 + aa / c
        c = c if abs(c) >= FPMIN else FPMIN
        de = d * c
        h *= de
        if abs(de - 1) < EPS:
            break
    return h


def betainc(a, b, x):
    if x <= 0:
        return 0.0
    if x >= 1:
        return 1.0
    bt = math.exp(math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b) + a * math.log(x) + b * math.log(1 - x))
    if x < (a + 1) / (a + b + 2):
        return bt * betacf(a, b, x) / a
    return 1 - bt * betacf(b, a, 1 - x) / b


def cp_lower(c, n, alpha):
    """One-sided exact lower bound: P(X >= c | p) = alpha, i.e. I_p(c, n-c+1) = alpha."""
    if c == 0:
        return 0.0
    lo, hi = 0.0, 1.0
    for _ in range(80):
        mid = (lo + hi) / 2
        if betainc(c, n - c + 1, mid) < alpha:
            lo = mid
        else:
            hi = mid
    return lo


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ek", type=float, default=0.02395)
    ap.add_argument("--ek-n", type=float, default=1e8)
    ap.add_argument("--s-nt", type=float, default=0.00113)
    ap.add_argument("--s-t", type=float, default=0.00118)
    ap.add_argument("--s-n", type=float, default=1e6, help="boards behind the I10 shares")
    ap.add_argument("--flags", type=int, default=600)
    ap.add_argument("--flags-u", type=int, default=1)
    ap.add_argument("--term", type=int, default=350)
    ap.add_argument("--term-u", type=int, default=0)
    a = ap.parse_args()
    ek_se = math.sqrt(1.6 * a.ek / a.ek_n)
    s_nt_se, s_t_se = math.sqrt(a.s_nt / a.s_n), math.sqrt(a.s_t / a.s_n)
    ncomp = 6
    alpha = 0.00135 / ncomp
    z = NormalDist().inv_cdf(1 - alpha)
    cap = CNT * (1 - a.s_nt) * (1 + a.ek) + CT * (1 - a.s_t)

    def lower(n1, u1):
        cnt = CNT * (1 - a.s_nt - z * s_nt_se)
        ct = CT * (1 - a.s_t - z * s_t_se)
        return (cnt * cp_lower(n1 - u1, n1, alpha) + cnt * (a.ek - z * ek_se) * cp_lower(a.flags - a.flags_u, a.flags, alpha)
                + ct * cp_lower(a.term - a.term_u, a.term, alpha))
    print(f"cap {cap:.4e}; Bonferroni over {ncomp} components, one-sided alpha {alpha:.2e} (z {z:.3f});"
          f" flags {a.flags}/u={a.flags_u}, terminal {a.term}/u={a.term_u}, I10 shares from {a.s_n:.0e} boards")
    for n1 in (20000, 40000, 80000):
        print(f"  n1={n1}: width " + " ".join(f"u={u}:{(cap - lower(n1, u)) / cap * 100:.2f}%" for u in (0, 20, 40, 80, 160, 320)))
    for target in (0.01, 0.005, 0.0025):
        out = []
        for n1 in (20000, 40000, 80000):
            best = -1
            lo, hi = 0, n1
            while lo < hi:                      # width is monotone in u
                mid = (lo + hi + 1) // 2
                if (cap - lower(n1, mid)) / cap <= target:
                    lo = mid
                else:
                    hi = mid - 1
            best = lo if (cap - lower(n1, 0)) / cap <= target else -1
            out.append(f"n1={n1}: u<={best} ({max(best, 0) / n1 * 100:.2f}%)")
        print(f"  width<={target * 100:.2f}%: " + "; ".join(out))


if __name__ == "__main__":
    main()
