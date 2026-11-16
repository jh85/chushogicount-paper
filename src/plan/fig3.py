#!/usr/bin/env python3
"""Figure 3 from the CSV of bayes.py: (a) posterior of |R| under the named priors on q
(median, 50 % and 99.73 % credible intervals) against the registered frequentist
bracket; (b) the posterior conditional on q, q from 0 to 1.  lishogi, Black to move.

Usage: python3 src/plan/fig3.py out/figures/fig3_bayes<suffix>.csv --lo 1.96967 --cap 1.97641
writes fig3a_bayes_priors<suffix>.svg and fig3b_bayes_q<suffix>.svg next to the CSV.
"""
import argparse
import csv
from pathlib import Path

W, H, X0, X1, Y0, Y1 = 720, 360, 150.0, 690.0, 64.0, 300.0
BLUE, GREY, INK, MUTED, GRID, BAND = "#3b6fd6", "#8c959f", "#1f2328", "#57606a", "#eaeef2", "#f1e9d2"
HEAD = (f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}" '
        f'font-family="Helvetica, Arial, sans-serif" font-size="12">\n<rect width="{W}" height="{H}" fill="#ffffff"/>')
THREE = 1.975
LABEL = {"q = 0": "q = 0", "q ~ Uniform": "q ~ Uniform(0, 1)", "q ~ Beta": "q ~ Beta(9, 1)", "q = 1": "q = 1"}


def _title(o, title, sub):
    o.append(f'<text x="64" y="22" font-size="15" font-weight="600" fill="{INK}">{title}</text>')
    o.append(f'<text x="64" y="40" fill="{MUTED}">{sub}</text>')


def fig3a(rows, lo, cap):
    pri = [r for r in rows if r["rule"] == "lishogi" and r["kind"] == "prior"]
    xa, xb = 1.9690, 1.9770
    X = lambda v: X0 + (v - xa) / (xb - xa) * (X1 - X0)
    o = [HEAD]
    _title(o, "Figure 3a. Posterior of |R| under four priors on q",
           "q = share of unresolved boards that are reachable; lishogi, Black to move, × 10^164")
    o.append(f'<rect x="{X(lo):.1f}" y="{Y0 - 8}" width="{X(cap) - X(lo):.1f}" height="{Y1 - Y0 + 8}" fill="{BAND}"/>')
    for i in range(9):
        v = xa + i * 0.001
        o.append(f'<line x1="{X(v):.1f}" y1="{Y0 - 8}" x2="{X(v):.1f}" y2="{Y1}" stroke="{GRID}" stroke-width="1"/>')
        o.append(f'<text x="{X(v):.1f}" y="{Y1 + 18}" text-anchor="middle" fill="{MUTED}">{v:.3f}</text>')
    o.append(f'<line x1="{X(THREE):.1f}" y1="{Y0 - 8}" x2="{X(THREE):.1f}" y2="{Y1}" stroke="{INK}" stroke-width="1" stroke-dasharray="4 3"/>')
    o.append(f'<text x="{X(THREE) + 4:.1f}" y="{Y0 + 2}" fill="{INK}">1.975</text>')
    step = (Y1 - Y0) / len(pri)
    for i, r in enumerate(pri):
        y = Y0 + step * (i + 0.5)
        med, l, h, q1, q3 = (float(r[k]) / 1e164 for k in ("median", "lo_99.73", "hi_99.73", "q25", "q75"))
        o.append(f'<text x="{X0 - 8}" y="{y + 4:.1f}" text-anchor="end" fill="{INK}">{next(v for k, v in LABEL.items() if r["scenario"].startswith(k))}</text>')
        o.append(f'<line x1="{X(l):.1f}" y1="{y:.1f}" x2="{X(h):.1f}" y2="{y:.1f}" stroke="{BLUE}" stroke-width="2"/>')
        o.append(f'<rect x="{X(q1):.1f}" y="{y - 6:.1f}" width="{max(X(q3) - X(q1), 1.5):.1f}" height="12" fill="{BLUE}" rx="2"/>')
        o.append(f'<circle cx="{X(med):.1f}" cy="{y:.1f}" r="3.5" fill="#ffffff" stroke="{INK}" stroke-width="1.2"/>')
        o.append(f'<text x="{X1 + 2}" y="{y - 10:.1f}" text-anchor="end" fill="{MUTED}">P(≥ 1.975) {float(r["p_ge_1.975"]):.2f}</text>')
    o += [f'<line x1="{X0}" y1="{Y1}" x2="{X1}" y2="{Y1}" stroke="{GREY}" stroke-width="1"/>',
          f'<text x="{(X0 + X1) / 2:.1f}" y="{Y1 + 40}" text-anchor="middle" fill="{INK}">|R| (× 10^164); shaded: registered bracket [{lo:.4f}, {cap:.4f}]; bar 50 %, line 99.73 %, circle median</text>',
          '</svg>']
    return "\n".join(o)


def fig3b(rows, lo, cap):
    qs = [r for r in rows if r["rule"] == "lishogi" and r["kind"] == "q"]
    ya, yb = 1.9690, 1.9770
    X = lambda q: X0 + q * (X1 - X0)
    Y = lambda v: Y1 - (v - ya) / (yb - ya) * (Y1 - Y0)
    o = [HEAD]
    _title(o, "Figure 3b. Posterior of |R| for a given q",
           "|R| × 10^164, lishogi, Black to move: median and 99.73 % credible band; dashed: 1.975")
    for i in range(9):
        v = ya + i * 0.001
        o.append(f'<line x1="{X0}" y1="{Y(v):.1f}" x2="{X1}" y2="{Y(v):.1f}" stroke="{GRID}" stroke-width="1"/>')
        o.append(f'<text x="{X0 - 8}" y="{Y(v) + 4:.1f}" text-anchor="end" fill="{MUTED}">{v:.3f}</text>')
    for i in range(6):
        q = i / 5
        o.append(f'<text x="{X(q):.1f}" y="{Y1 + 18}" text-anchor="middle" fill="{MUTED}">{q:.1f}</text>')
    pts = [(float(r["scenario"]), float(r["lo_99.73"]) / 1e164, float(r["hi_99.73"]) / 1e164, float(r["median"]) / 1e164) for r in qs]
    band = " ".join(f"{X(q):.1f},{Y(h):.1f}" for q, _, h, _ in pts) + " " + " ".join(f"{X(q):.1f},{Y(l):.1f}" for q, l, _, _ in reversed(pts))
    o.append(f'<polygon points="{band}" fill="#cddbf6" stroke="none"/>')
    o.append(f'<polyline points="{" ".join(f"{X(q):.1f},{Y(m):.1f}" for q, _, _, m in pts)}" fill="none" stroke="{BLUE}" stroke-width="2"/>')
    for v, label in ((lo, "registered lower end"), (cap, "cap")):
        o.append(f'<line x1="{X0}" y1="{Y(v):.1f}" x2="{X1}" y2="{Y(v):.1f}" stroke="{GREY}" stroke-width="1"/>')
        o.append(f'<text x="{X0 + 6}" y="{Y(v) - 4:.1f}" fill="{MUTED}">{label} {v:.4f}</text>')
    o.append(f'<line x1="{X0}" y1="{Y(THREE):.1f}" x2="{X1}" y2="{Y(THREE):.1f}" stroke="{INK}" stroke-width="1" stroke-dasharray="4 3"/>')
    o += [f'<line x1="{X0}" y1="{Y1}" x2="{X1}" y2="{Y1}" stroke="{GREY}" stroke-width="1"/>',
          f'<text x="{(X0 + X1) / 2:.1f}" y="{Y1 + 40}" text-anchor="middle" fill="{INK}">q, share of the unresolved boards that are reachable</text>',
          '</svg>']
    return "\n".join(o)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("csv")
    ap.add_argument("--lo", type=float, required=True)
    ap.add_argument("--cap", type=float, required=True)
    a = ap.parse_args()
    rows = list(csv.DictReader(open(a.csv)))
    p = Path(a.csv)
    sfx = p.stem.replace("fig3_bayes", "")
    (p.parent / f"fig3a_bayes_priors{sfx}.svg").write_text(fig3a(rows, a.lo, a.cap))
    (p.parent / f"fig3b_bayes_q{sfx}.svg").write_text(fig3b(rows, a.lo, a.cap))


if __name__ == "__main__":
    main()
