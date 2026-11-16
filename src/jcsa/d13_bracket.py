#!/usr/bin/env python3
"""Bracket for the D13 non-terminal term (registered for run M-G13, runs.md).

N13 = number of non-terminal candidate boards (Black to move, flag cleared) reachable under
the literal JCSA checkmate ending (D13, D13a): the p1 term of |R| under D13.  From the
records of d13_pilot.py on a uniform sample of C_nt (I10 boards excluded from n, as in the
registered M-F bracket; unresolved boards stay in n):
    q_lo = CP lower bound of certified / n'
    q_hi = 1 - CP lower bound of (retracted + retracted2) / n'
    L = |C_nt| (1 - s_nt - z sd_nt) q_lo,   U = |C_nt| (1 - s_nt + z sd_nt) q_hi
Joint coverage >= 99.73 %: Bonferroni over four one-sided components (certified, proven
unreachable, s_nt at each end) at α = 0.0027 / 4.
Decision rule: claim N13 to two significant digits iff L and U round (half up) to the same
two-digit value.

--override FILE (re-analysis G13b under D13b, runs.md): records of FILE replace the records of
the same seed (every seed of FILE must be in the main records); records not replaced keep their
class, which is valid only for certified ones (a D13 certificate is a D13b certificate), so
every non-certified record must be replaced.

Usage: python3 src/jcsa/d13_bracket.py out/runs/d13_run_g13.jsonl [--override out/runs/d13_run_g13b.jsonl]
"""
import argparse
import json
import sys
from collections import Counter
from decimal import Decimal, ROUND_HALF_UP
from pathlib import Path
from statistics import NormalDist

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.candidates import chu_setup, count      # noqa: E402
from plan.budget import cp_lower                    # noqa: E402
from plan.estimate import I10_SHARE                 # noqa: E402

ALPHA = 0.0027 / 4


def two_digits(x):
    d = Decimal(repr(x))
    e = d.adjusted()
    return (d.scaleb(-e).quantize(Decimal("0.1"), rounding=ROUND_HALF_UP), e)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("records")
    ap.add_argument("--override")
    a = ap.parse_args()
    rows = [json.loads(l) for l in open(a.records)]
    assert len({r["seed"] for r in rows}) == len(rows), "duplicate seeds"
    if a.override:
        new = {r["seed"]: r for r in map(json.loads, open(a.override))}
        seeds = {r["seed"] for r in rows}
        assert set(new) <= seeds, "override seeds outside the main records"
        rows = [new.get(r["seed"], r) for r in rows]
        left = [r["seed"] for r in rows if r["seed"] not in new and r["d13"] not in ("certified", "I10")]
        assert not left, f"{len(left)} non-certified records not replaced"
        print(f"override: {len(new)} records replaced from {a.override}")
    c = Counter(r["d13"] for r in rows)
    n = len(rows) - c["I10"]
    cert, unr, unres = c["certified"], c["retracted"] + c["retracted2"], c["unresolved"]
    assert cert + unr + unres == n, c
    q_lo, q_hi = cp_lower(cert, n, ALPHA), 1 - cp_lower(unr, n, ALPHA)
    s, sd = I10_SHARE["nonterm"]
    z = NormalDist().inv_cdf(1 - ALPHA)
    cn = count(chu_setup("file", identify_royals=True), "file", colour=True).total
    lo, hi = cn * (1 - s - z * sd) * q_lo, cn * (1 - s + z * sd) * q_hi
    print(f"records {len(rows)}: {dict(c)}; n' = {n} (I10 excluded)")
    print(f"|C_nt| = {cn}; s_nt {s} ± {sd} (1σ); α = {ALPHA:.6f} per component, z = {z:.3f}")
    print(f"D13 share q in [{q_lo:.5f}, {q_hi:.5f}] (point {cert / n:.5f} certified, {1 - unr / n:.5f} not proven unreachable)")
    print(f"N13 in [{lo:.5e}, {hi:.5e}] (Black to move), width (U - L)/U {(hi - lo) / hi * 100:.3f} %")
    dl, du = two_digits(lo), two_digits(hi)
    if dl == du:
        print(f"decision: two significant digits, N13 = {dl[0]} x 10^{dl[1]}")
    else:
        print(f"decision: not two digits (bounds round to {dl[0]}e{dl[1]} and {du[0]}e{du[1]})")


if __name__ == "__main__":
    main()
