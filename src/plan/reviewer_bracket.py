#!/usr/bin/env python3
"""The construction of the external review of sampling precision (2026-10-30, §4–5) applied
to |R| for run M-F, lishogi, for docs/reviews/response-sampling-precision.md.

Per stratum: lower Clopper-Pearson bound with a certified, upper with a + u successes (= 1 - lower
bound on the b proven-unreachable samples), two-sided error 0.0027 split equally over all
one-sided statements; I10 boards count as binomial failures in n and no static I10 share is
used.  The review omitted E[k]; it is added here as one more component at each end (normal).
Prints the per-stratum intervals of the review (check) and the resulting |R| bracket.

Usage: python3 src/plan/reviewer_bracket.py
"""
import sys
from pathlib import Path
from statistics import NormalDist

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.candidates import chu_setup, count       # noqa: E402
from plan.budget import cp_lower                     # noqa: E402
from plan.estimate import EK, EK_SE                  # noqa: E402

# stratum: (n, certified, proven unreachable, unresolved), run M-F, lishogi
MF = {"nonterm": (400000, 399355, 487, 158), "flags": (40000, 39938, 45, 17), "term": (24000, 23965, 25, 10)}


def main():
    cn = count(chu_setup("file", identify_royals=True), "file", colour=True).total
    ct = count(chu_setup("file", identify_royals=True, terminal_only=True), "file", colour=True).total
    for nstat, label in ((6, "review's split (3 strata x 2 ends), E[k] at the same level"),
                         (8, "E[k] as two further statements")):
        tau = 0.0027 / nstat
        z = NormalDist().inv_cdf(1 - tau)
        lo_p = {k: cp_lower(a, n, tau) for k, (n, a, b, u) in MF.items()}
        hi_p = {k: 1 - cp_lower(b, n, tau) for k, (n, a, b, u) in MF.items()}
        lo = cn * lo_p["nonterm"] + cn * (EK - z * EK_SE) * lo_p["flags"] + ct * lo_p["term"]
        hi = cn * hi_p["nonterm"] + cn * (EK + z * EK_SE) * hi_p["flags"] + ct * hi_p["term"]
        print(f"{label}: tau = {tau:.6f}")
        for k in MF:
            print(f"  {k}: [{lo_p[k]:.7f}, {hi_p[k]:.7f}]")
        print(f"  |R| in [{lo / 1e164:.5f}, {hi / 1e164:.5f}] x 10^164; three digits (1.98): "
              f"{lo >= 1.975e164 and hi < 1.985e164}")


if __name__ == "__main__":
    main()
