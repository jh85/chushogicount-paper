#!/usr/bin/env python3
"""Supplementary strict bracket (registered for run M-E, runs.md), next to the registered one.

Reads the per-sample records of a main run, the paired flag log (flags.py --jcsa) and the
I10 log (lanes.py); does not touch the registered estimator (estimate.py).  Differences
from the registered bracket:
  - cap: both I10 shares at their lower bound s - zσ and E[k] at its upper bound E[k] + zσ,
    U = |C_nt|(1 - s_nt^lo) + |C_nt| E[k]^hi + |C_t|(1 - s_t^lo)
    (the flag term without a (1 - s) factor, so no independence of k and I10 is assumed);
  - lower end, flag term: a lower bound on E[k·1_{¬I10}] = E[k] - E[k·1_I10] (two
    independent samples, one normal component; Var(k·1_I10) <= 3 E[k·1_I10] since k <= 3),
    times p2 among the non-I10 flag samples, as registered.  Under JCSA, where E[k·1_I10]
    is not measured, the flag term is |C_nt| E[k]_JCSA^lo · p2', with p2' the fraction of
    all JCSA flag samples certified (I10 samples in the denominator, counted unreachable);
  - α: each endpoint is one-sided at α = 0.00135 on its own (joint coverage of the bracket
    >= 1 - 2α = 99.73 %): lower end Bonferroni over six components (p1 p2 p3, the flag
    factor, s_nt, s_t) at α/6, upper end over three (E[k], s_nt, s_t) at α/3.

Usage: python3 src/plan/strict_bracket.py --records out/runs/<main>.jsonl \
           --flags out/runs/flags_jcsa_<...>.log --lanes out/runs/lanes_<...>.log
"""
import argparse
import ast
import json
import math
import re
import sys
from pathlib import Path
from statistics import NormalDist

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.candidates import chu_setup, count      # noqa: E402
from plan.budget import cp_lower                    # noqa: E402

ALPHA = 0.00135


def flag_moments(path):
    """E[k] and its σ for lishogi and JCSA from the (k_lishogi, k_jcsa) table of a paired log."""
    line = next(l for l in Path(path).read_text().splitlines() if "by (k_lishogi, k_jcsa):" in l)
    joint = ast.literal_eval(line.split(":", 1)[1].strip())
    n = sum(joint.values())
    out = {}
    for i, rule in ((0, "lishogi"), (1, "JCSA")):
        m1 = sum(k[i] * v for k, v in joint.items()) / n
        m2 = sum(k[i] ** 2 * v for k, v in joint.items()) / n
        out[rule] = (m1, math.sqrt((m2 - m1 ** 2) / n))
    return out, max(max(k) for k in joint)


def i10(path):
    """(share, σ) per stratum and (E[k·1_I10], σ bound) from a lanes.py log."""
    txt = Path(path).read_text()
    out = {}
    for name, key in (("non-terminal", "nonterm"), ("terminal", "term")):
        m = re.search(rf"^{name}: (\d+)/(\d+) violate I10", txt, re.M)
        bad, n = int(m.group(1)), int(m.group(2))
        p = bad / n
        out[key] = (p, math.sqrt(p * (1 - p) / n))
        if key == "nonterm":
            fb = int(re.search(r"effective-flag states on violating boards: (\d+)", txt).group(1))
            e = fb / n
            out["ek_i10"] = (e, math.sqrt(3 * e / n))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--records", required=True)
    ap.add_argument("--flags", required=True)
    ap.add_argument("--lanes", required=True)
    a = ap.parse_args()
    recs = [json.loads(l) for l in open(a.records)]
    ek, kmax = flag_moments(a.flags)
    assert kmax <= 3, kmax
    sh = i10(a.lanes)
    cn = count(chu_setup("file", identify_royals=True), "file", colour=True).total
    ct = count(chu_setup("file", identify_royals=True, terminal_only=True), "file", colour=True).total
    a_lo, a_hi = ALPHA / 6, ALPHA / 3
    z_lo, z_hi = NormalDist().inv_cdf(1 - a_lo), NormalDist().inv_cdf(1 - a_hi)
    (s_nt, sd_nt), (s_t, sd_t), (e10, sd_e10) = sh["nonterm"], sh["term"], sh["ek_i10"]
    print(f"|C_nt| = {cn:.6e}, |C_t| = {ct:.6e}; s_nt {s_nt:.6f} ± {sd_nt:.6f}, s_t {s_t:.6f} ± {sd_t:.6f} (1σ);"
          f" E[k·1_I10] {e10:.3e} ± {sd_e10:.1e} (1σ bound); z_lo {z_lo:.3f} (α/6), z_hi {z_hi:.3f} (α/3)")

    def stratum(name, ok, all_in_n=False):
        rs = [r for r in recs if r["stratum"] == name]
        n = len(rs) if all_in_n else sum(1 for r in rs if not r["result"].get("unreachable"))
        return sum(1 for r in rs if ok(r["result"])), n

    for rule in ("lishogi", "JCSA"):
        if rule == "lishogi":
            ok = lambda res: bool(res.get("ok"))
            c1, n1 = stratum("nonterm", ok)
            c2, n2 = stratum("flags", ok)
            m, sd = ek["lishogi"][0] - e10, math.hypot(ek["lishogi"][1], sd_e10)
        else:
            if not any(r["stratum"] == "flagsj" for r in recs):
                continue
            ok = lambda res: bool(res.get("ok")) and bool(res.get("jcsa_ok"))
            c1, n1 = stratum("nonterm", ok)
            c2, n2 = stratum("flagsj", ok, all_in_n=True)
            m, sd = ek["JCSA"]
        c3, n3 = stratum("term", ok)
        p1, p2, p3 = cp_lower(c1, n1, a_lo), cp_lower(c2, n2, a_lo), cp_lower(c3, n3, a_lo)
        lo = cn * (1 - s_nt - z_lo * sd_nt) * p1 + cn * (m - z_lo * sd) * p2 + ct * (1 - s_t - z_lo * sd_t) * p3
        e, esd = ek[rule]
        hi = cn * (1 - s_nt + z_hi * sd_nt) + cn * (e + z_hi * esd) + ct * (1 - s_t + z_hi * sd_t)
        print(f"{rule} strict bracket: |R| in [{lo:.5e}, {hi:.5e}] (Black to move), width (U - L)/U {(hi - lo) / hi * 100:.3f} %;"
              f" x2 [{2 * lo:.4e}, {2 * hi:.4e}]; p1 {c1}/{n1} >= {p1:.5f}, p2 {c2}/{n2} >= {p2:.5f}, p3 {c3}/{n3} >= {p3:.5f};"
              f" flag factor >= {m - z_lo * sd:.6f}, E[k] <= {e + z_hi * esd:.6f};"
              f" each endpoint one-sided α = {ALPHA} (joint >= {100 * (1 - 2 * ALPHA):.2f} %)")


if __name__ == "__main__":
    main()
