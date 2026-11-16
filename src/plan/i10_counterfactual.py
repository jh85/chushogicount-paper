#!/usr/bin/env python3
"""Counterfactual for docs/notes-I10.md: run M-F's registered lishogi bracket with and without I10.

Counts from docs/results-F.md.  With I10 this reproduces the registered bracket (estimate.py
registered_brackets).  Without I10 there is no I10 share and no sample is proven unreachable
(every proven-unreachable M-F sample is an I10 violation), so those samples stay in n and count
as unresolved; Bonferroni over 4 components (three strata, E[k]) or 6 as registered.

Usage: python3 src/plan/i10_counterfactual.py
"""
import sys
from pathlib import Path
from statistics import NormalDist

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.candidates import chu_setup, count       # noqa: E402
from plan.budget import cp_lower                     # noqa: E402
from plan.estimate import EK, EK_SE, I10_SHARE       # noqa: E402

# stratum: (n, certified, proven unreachable by I10), run M-F, lishogi
MF = {"nonterm": (400000, 399355, 487), "flags": (40000, 39938, 45), "term": (24000, 23965, 25)}


def bracket(cn, ct, use_i10, ncomp):
    alpha = 0.00135 / ncomp
    z = NormalDist().inv_cdf(1 - alpha)
    s_nt, sd_nt = I10_SHARE["nonterm"] if use_i10 else (0, 0)
    s_t, sd_t = I10_SHARE["term"] if use_i10 else (0, 0)
    p = {k: cp_lower(c, n - u if use_i10 else n, alpha) for k, (n, c, u) in MF.items()}
    w_nt, w_t = cn * (1 - s_nt - z * sd_nt), ct * (1 - s_t - z * sd_t)
    lo = w_nt * p["nonterm"] + w_nt * (EK - z * EK_SE) * p["flags"] + w_t * p["term"]
    hi = cn * (1 - s_nt) * (1 + EK) + ct * (1 - s_t)
    return lo, hi


def main():
    cn = count(chu_setup("file", identify_royals=True), "file", colour=True).total
    ct = count(chu_setup("file", identify_royals=True, terminal_only=True), "file", colour=True).total
    for use_i10, ncomp in ((True, 6), (False, 4), (False, 6)):
        lo, hi = bracket(cn, ct, use_i10, ncomp)
        three = lo >= 1.975e164 and hi < 1.985e164
        print(f"I10 {'used' if use_i10 else 'not used'}, Bonferroni over {ncomp}: "
              f"[{lo / 1e164:.5f}, {hi / 1e164:.5f}] x 10^164, width {(hi - lo) / hi * 100:.3f} %, "
              f"three digits (1.98): {three}")


if __name__ == "__main__":
    main()
