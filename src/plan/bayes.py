#!/usr/bin/env python3
"""Bayesian sensitivity analysis of a main run's count (exploratory; runs.md, "M-E Bayesian
sensitivity analysis").  Not part of the registered result.

Model (Black to move):
  |R| = |C_nt| (1 - s_nt) p1 + |C_nt| m p2 + |C_t| (1 - s_t) p3,    p_i = a_i + u_i q
  a_i, u_i  certified and unresolved shares of the admissible samples of stratum i
            (I10 samples excluded, as registered): Beta(c + h, u + h) posterior, h = 1
            (flat) or 1/2 (Jeffreys);
  s_nt, s_t I10 shares: Beta(bad + h, n - bad + h) from the lanes log;
  m         flag states per board on non-I10 boards, E[k] - E[k 1_I10]: normal for E[k]
            (10^8 boards), Gamma(count + h) / n for E[k 1_I10]; no independence of k and
            I10 assumed (as the strict bracket).  Under JCSA, m = E[k]_JCSA and p2 is taken
            over all JCSA flag samples (I10 samples counted unresolved-unreachable, q = 0);
  q         fraction of the unresolved samples that are reachable, one q for all strata.
            The data carry no information on q (an unresolved sample is undecided), so q
            is the assumption under test: point values on a grid, and named priors.
|C_nt|, |C_t| are exact.  Monte Carlo with common random numbers across scenarios.

Usage: python3 src/plan/bayes.py --records out/runs/<main>.jsonl --flags out/runs/flags_jcsa_<...>.log
           --lanes out/runs/lanes_<...>.log [--followup out/runs/<main>_followup.jsonl] [--n 400000]
           [--seed 1] [--jeffreys] [--csv out/figures/fig3_bayes.csv]
"""
import argparse
import ast
import json
import math
import random
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.candidates import chu_setup, count      # noqa: E402

THREE = 1.975e164                                   # rounds to 1.98 at three digits iff |R| >= THREE
PRIORS = (("q = 0 (all unreachable)", lambda r: 0.0),
          ("q ~ Uniform(0, 1)", lambda r: r.random()),
          ("q ~ Beta(9, 1), mean 0.9", lambda r: r.betavariate(9, 1)),
          ("q = 1 (all reachable)", lambda r: 1.0))


def joint_table(path):
    line = next(l for l in Path(path).read_text().splitlines() if "by (k_lishogi, k_jcsa):" in l)
    return ast.literal_eval(line.split(":", 1)[1].strip())


def moments(joint, i):
    n = sum(joint.values())
    m1 = sum(k[i] * v for k, v in joint.items()) / n
    m2 = sum(k[i] ** 2 * v for k, v in joint.items()) / n
    return m1, math.sqrt((m2 - m1 * m1) / n)


def lanes(path):
    txt = Path(path).read_text()
    out = {}
    for name, key in (("non-terminal", "nt"), ("terminal", "t")):
        m = re.search(rf"^{name}: (\d+)/(\d+) violate I10", txt, re.M)
        out[key] = (int(m.group(1)), int(m.group(2)))
    out["fb"] = int(re.search(r"effective-flag states on violating boards: (\d+)", txt).group(1))
    return out


def strata(records, rescued):
    """(certified, unresolved) per stratum and rule set; I10 samples excluded except in the
    JCSA flag stratum, where they count as unresolved with q = 0 (returned separately)."""
    out = {}
    for rule in ("lishogi", "JCSA"):
        for s in ("nonterm", "flags", "term", "flagsj"):
            rs = [r for r in records if r["stratum"] == s]
            if rule == "lishogi":
                ok = lambda r: bool(r["result"].get("ok")) or (s == "nonterm" and r["seed"] in rescued)
            else:
                ok = lambda r: (bool(r["result"].get("ok")) and bool(r["result"].get("jcsa_ok"))) or \
                               (s == "nonterm" and rescued.get(r["seed"]) is True)
            c = sum(1 for r in rs if ok(r))
            i10 = sum(1 for r in rs if r["result"].get("unreachable"))
            out[rule, s] = (c, len(rs) - c - i10, i10)
    return out


def quantile(xs, p):
    return xs[min(len(xs) - 1, max(0, int(round(p * (len(xs) - 1)))))]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--records", required=True)
    ap.add_argument("--flags", required=True)
    ap.add_argument("--lanes", required=True)
    ap.add_argument("--followup", action="append", default=[], help="repeatable")
    ap.add_argument("--n", type=int, default=400000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--jeffreys", action="store_true")
    ap.add_argument("--csv")
    a = ap.parse_args()
    h = 0.5 if a.jeffreys else 1.0
    recs = [json.loads(l) for l in open(a.records)]
    rescued = {}
    for path in a.followup:
        for r in map(json.loads, open(path)):
            if r["certified"]:
                rescued[r["seed"]] = bool(r.get("jcsa_ok"))
    st = strata(recs, rescued)
    joint, ln = joint_table(a.flags), lanes(a.lanes)
    cn = count(chu_setup("file", identify_royals=True), "file", colour=True).total
    ct = count(chu_setup("file", identify_royals=True, terminal_only=True), "file", colour=True).total
    (ek, ek_se), (ekj, ekj_se) = moments(joint, 0), moments(joint, 1)
    rng = random.Random(a.seed)
    N = a.n

    def beta(x, y):
        return [rng.betavariate(x + h, y + h) for _ in range(N)]

    s_nt, s_t = beta(ln["nt"][0], ln["nt"][1] - ln["nt"][0]), beta(ln["t"][0], ln["t"][1] - ln["t"][0])
    e10 = [rng.gammavariate(ln["fb"] + h, 1.0) / ln["nt"][1] for _ in range(N)]
    ekL = [rng.gauss(ek, ek_se) for _ in range(N)]
    ekJ = [rng.gauss(ekj, ekj_se) for _ in range(N)]
    print(f"|C_nt| {cn:.6e}, |C_t| {ct:.6e}; E[k] {ek:.5f} ± {ek_se:.1e}, E[k]_JCSA {ekj:.5f} ± {ekj_se:.1e},"
          f" E[k 1_I10] {ln['fb'] / ln['nt'][1]:.2e}; prior h = {h}; N = {N}, seed {a.seed};"
          f" follow-up rescues {len(rescued)}")

    def shares(c, u, extra=0):
        """Draws of (a, u, z): certified, unresolved and (JCSA flags) I10 share."""
        if extra:
            out = []
            for _ in range(N):
                g = [rng.gammavariate(x + h, 1.0) for x in (c, u, extra)]
                t = sum(g)
                out.append((g[0] / t, g[1] / t))
            return out
        return [(b, 1 - b) for b in beta(c, u)]

    draws = {}
    for rule in ("lishogi", "JCSA"):
        c1, u1, _ = st[rule, "nonterm"]
        c3, u3, _ = st[rule, "term"]
        if rule == "lishogi":
            c2, u2, _ = st[rule, "flags"]
            f2 = shares(c2, u2)
        else:
            c2, u2, i2 = st[rule, "flagsj"]
            f2 = shares(c2, u2, i2)
        draws[rule] = (shares(c1, u1), f2, shares(c3, u3))
        print(f"{rule}: non-terminal {c1} certified / {u1} unresolved; flag {c2} / {u2}; terminal {c3} / {u3}")

    def R(rule, qs):
        f1, f2, f3 = draws[rule]
        out = []
        for j in range(N):
            q = qs[j]
            p1, p2, p3 = f1[j][0] + f1[j][1] * q, f2[j][0] + f2[j][1] * q, f3[j][0] + f3[j][1] * q
            m = ekL[j] - e10[j] if rule == "lishogi" else ekJ[j]
            out.append(cn * (1 - s_nt[j]) * p1 + cn * m * p2 + ct * (1 - s_t[j]) * p3)
        out.sort()
        return out

    def summary(xs):
        return (quantile(xs, 0.5), quantile(xs, 0.00135), quantile(xs, 0.99865), quantile(xs, 0.25), quantile(xs, 0.75),
                sum(1 for x in xs if x >= THREE) / len(xs))

    rows = []
    qrng = random.Random(a.seed + 1)
    for rule in ("lishogi", "JCSA"):
        print(f"\n{rule}, named priors on q (× 10^164; 99.73 % equal-tailed credible interval):")
        for name, f in PRIORS:
            xs = R(rule, [f(qrng) for _ in range(N)])
            med, lo, hi, q1, q3, p3 = summary(xs)
            rows.append((rule, "prior", name, med, lo, hi, q1, q3, p3))
            print(f"  {name:28s} median {med / 1e164:.5f}  [{lo / 1e164:.5f}, {hi / 1e164:.5f}]"
                  f"  50 % [{q1 / 1e164:.5f}, {q3 / 1e164:.5f}]" + (f"  P(|R| >= 1.975) {p3:.3f}" if rule == "lishogi" else ""))
    print("\nlishogi, conditional on q (grid):")
    for i in range(21):
        q = i / 20
        xs = R("lishogi", [q] * N)
        med, lo, hi, q1, q3, p3 = summary(xs)
        rows.append(("lishogi", "q", f"{q:.2f}", med, lo, hi, q1, q3, p3))
        print(f"  q = {q:.2f}: median {med / 1e164:.5f}  [{lo / 1e164:.5f}, {hi / 1e164:.5f}]  P(|R| >= 1.975) {p3:.3f}")
    if a.csv:
        with open(a.csv, "w") as fh:
            fh.write("rule,kind,scenario,median,lo_99.73,hi_99.73,q25,q75,p_ge_1.975\n")
            for r in rows:
                fh.write(",".join([r[0], r[1], f'"{r[2]}"'] + [f"{x:.6e}" for x in r[3:8]] + [f"{r[8]:.4f}"]) + "\n")


if __name__ == "__main__":
    main()
