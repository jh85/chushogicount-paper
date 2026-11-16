#!/usr/bin/env python3
"""Figure 2 from a main run's per-sample records: (a) certificate lengths of the certified
non-terminal boards, bins of 250 plies; (b) retraction depths of the certificates rescued
by relaxation, all strata.

Usage: python3 src/plan/fig2.py out/runs/<main>.jsonl out/figures/<suffix>
writes fig2_certificates<suffix>.csv, fig2a_certificate_lengths<suffix>.svg and
fig2b_relaxation_depths<suffix>.svg (same layout as the 2026-10-11 figures).
"""
import json
import statistics
import sys
from collections import Counter
from pathlib import Path

BASE, TOP, X0, X1 = 308.0, 56.0, 65.0, 701.0
HEAD = ('<svg xmlns="http://www.w3.org/2000/svg" width="720" height="360" viewBox="0 0 720 360" '
        'font-family="Helvetica, Arial, sans-serif" font-size="12">\n<rect width="720" height="360" fill="#ffffff"/>')


def _tick(v):
    return f"{float(f'{v:.3g}'):,.0f}"


def _svg(title, sub, counts, labels, xlabel, gap):
    """counts: bar heights in order; labels: {bar index: text}."""
    top = max(counts) * 1.08
    o = [HEAD, f'<text x="64" y="22" font-size="15" font-weight="600" fill="#1f2328">{title}</text>',
         f'<text x="64" y="40" fill="#57606a">{sub}</text>']
    for i in range(5):
        y = BASE - i * (BASE - TOP) / 4
        o.append(f'<line x1="64" y1="{y:.1f}" x2="700" y2="{y:.1f}" stroke="#eaeef2" stroke-width="1"/>')
        o.append(f'<text x="56" y="{y + 4:.1f}" text-anchor="end" fill="#57606a">{_tick(top * i / 4) if i else 0}</text>')
    step = (X1 - X0) / len(counts)
    for i, c in enumerate(counts):
        h = c / top * (BASE - TOP)
        o.append(f'<rect x="{X0 + i * step:.1f}" y="{BASE - h:.1f}" width="{step - gap:.1f}" height="{h:.1f}" fill="#3b6fd6" rx="2"/>')
    for i, t in labels.items():
        o.append(f'<text x="{X0 + i * step + (step - gap) / 2:.1f}" y="326" text-anchor="middle" fill="#57606a">{t}</text>')
    o += ['<line x1="64" y1="308" x2="700" y2="308" stroke="#8c959f" stroke-width="1"/>',
          f'<text x="382.0" y="350" text-anchor="middle" fill="#1f2328">{xlabel}</text>',
          '<text x="14" y="182.0" transform="rotate(-90 14 182.0)" text-anchor="middle" fill="#1f2328">certificates</text>',
          '</svg>']
    return "\n".join(o)


def main(records, stem):
    recs = [json.loads(l) for l in open(records)]
    plies = [r["result"]["plies"] for r in recs if r["stratum"] == "nonterm" and r["result"].get("ok")]
    bins = Counter(p // 250 for p in plies)
    nb = max(26, max(bins) + 2)
    lengths = [bins.get(i, 0) for i in range(nb)]
    depth = Counter(r["result"]["rescued"] for r in recs if r["result"].get("ok") and r["result"].get("rescued"))
    ds = sorted(depth)
    d = Path(stem).parent
    d.mkdir(parents=True, exist_ok=True)
    sfx = Path(stem).name
    (d / f"fig2_certificates{sfx}.csv").write_text(
        "plies_bin_start,count\n" + "".join(f"{i * 250},{c}\n" for i, c in enumerate(lengths))
        + "\nretraction_plies,count\n" + "".join(f"{k},{depth[k]}\n" for k in ds))
    (d / f"fig2a_certificate_lengths{sfx}.svg").write_text(_svg(
        "Figure 2a. Certificate lengths, main run",
        f"{len(plies)} certified non-terminal boards; median {statistics.median(plies):.0f} plies, longest {max(plies)}",
        lengths, {i: str(i * 250) for i in range(0, nb, 4)}, "plies (bins of 250)", 2.0))
    if len(ds) <= 20:
        bars, labels, xlabel = [depth[k] for k in ds], {i: str(k) for i, k in enumerate(ds)}, "retracted plies"
    else:                                   # deep cascades (run M-F): 1-5 singly, then doubling bins
        edges = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 10), (11, 20), (21, 40), (41, 80), (81, max(ds))]
        bars = [sum(depth[k] for k in ds if a <= k <= b) for a, b in edges]
        labels = {i: str(a) if a == b else f"{a}–{b}" if i < len(edges) - 1 else f"{a}+" for i, (a, b) in enumerate(edges)}
        xlabel = "retracted plies (bins)"
    (d / f"fig2b_relaxation_depths{sfx}.svg").write_text(_svg(
        "Figure 2b. Retro-relaxation depths, main run",
        f"{sum(depth.values())} certificates rescued by relaxation; retraction plies before the planner succeeded",
        bars, labels, xlabel, 2.0))
    allp = [r["result"]["plies"] for r in recs if r["result"].get("ok")]
    print(f"non-terminal: {len(plies)} certificates, median {statistics.median(plies):.0f}, longest {max(plies)};"
          f" all strata: {len(allp)}, mean {sum(allp) / len(allp):.0f}, longest {max(allp)};"
          f" rescued {sum(depth.values())} by depth {dict(sorted(depth.items()))}")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
