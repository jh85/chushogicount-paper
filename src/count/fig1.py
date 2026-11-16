#!/usr/bin/env python3
"""Figure 1: exact marginal of |C| (primary, Black to move) by pieces on the board.

Usage: python3 src/count/fig1.py out/figures/fig1_pieces_on_board.v1.1
writes <stem>.csv and <stem>.svg (same layout as the 2026-10-11 figure).
"""
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from count.candidates import PRIMARY, chu_setup, count      # noqa: E402

LO, HI = 68, 88
X0, STEP, BAR, BASE, SCALE = 66.0, 30.3, 26.3, 308.0, 700.0


def main(stem):
    Path(stem).parent.mkdir(parents=True, exist_ok=True)
    r = count(chu_setup("file", **PRIMARY), "file", colour=True, stats=True, dist=True)
    tot = r.total
    share = {n: Fraction(r.by_pieces.get(n, 0), tot) for n in range(93)}
    mean = float(sum(n * s for n, s in share.items()))
    mode = max(share, key=share.get)
    outside = float(1 - sum(share[n] for n in range(LO, HI + 1)))
    Path(stem + ".csv").write_text("pieces,share\n" + "".join(f"{n},{float(s):.6e}\n" for n, s in share.items()))
    o = ['<svg xmlns="http://www.w3.org/2000/svg" width="720" height="360" viewBox="0 0 720 360" '
         'font-family="Helvetica, Arial, sans-serif" font-size="12">',
         '<rect width="720" height="360" fill="#ffffff"/>',
         '<text x="64" y="22" font-size="15" font-weight="600" fill="#1f2328">Figure 1. Pieces on the board over the candidate set</text>']
    mant, ex = f"{outside:.0e}".split("e")
    sup = str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹")
    o.append(f'<text x="64" y="40" fill="#57606a">exact marginal of |C| (Black to move); {LO}–{HI} pieces shown, '
             f'{mant}×10⁻{str(-int(ex)).translate(sup)} outside; mean {mean:.2f}, mode {mode}</text>')
    for i in range(5):
        v = 0.09 * i
        y = BASE - v * SCALE
        o.append(f'<line x1="64" y1="{y:.1f}" x2="700" y2="{y:.1f}" stroke="#eaeef2" stroke-width="1"/>')
        o.append(f'<text x="56" y="{y + 4:.1f}" text-anchor="end" fill="#57606a">{v:.2f}</text>')
    for i, n in enumerate(range(LO, HI + 1)):
        x, h = X0 + i * STEP, float(share[n]) * SCALE
        o.append(f'<rect x="{x:.1f}" y="{BASE - h:.1f}" width="{BAR}" height="{h:.1f}" fill="#3b6fd6" rx="2"/>')
        if share[n] >= Fraction(5, 100):
            o.append(f'<text x="{x + BAR / 2:.1f}" y="{BASE - h - 5:.1f}" text-anchor="middle" fill="#1f2328" '
                     f'font-size="11">{float(share[n]) * 100:.1f}%</text>')
    for i, n in enumerate(range(LO, HI + 1)):
        if n % 2 == 0:
            o.append(f'<text x="{X0 + i * STEP + BAR / 2:.1f}" y="326" text-anchor="middle" fill="#57606a">{n}</text>')
    o += ['<line x1="64" y1="308" x2="700" y2="308" stroke="#8c959f" stroke-width="1"/>',
          '<text x="382.0" y="350" text-anchor="middle" fill="#1f2328">pieces on the board (of 92)</text>',
          '<text x="14" y="182.0" transform="rotate(-90 14 182.0)" text-anchor="middle" fill="#1f2328">share of candidate boards</text>',
          '</svg>']
    Path(stem + ".svg").write_text("\n".join(o) + "\n")
    print(f"mean {mean:.4f}, mode {mode}, support {min(n for n in share if share[n])}–{max(n for n in share if share[n])}, "
          f"outside {LO}–{HI}: {outside:.2e}")


if __name__ == "__main__":
    main(sys.argv[1])
