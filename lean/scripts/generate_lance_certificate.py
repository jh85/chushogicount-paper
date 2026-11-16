#!/usr/bin/env python3
"""Propose lance reachability witnesses and a complete closed-state certificate.

Lean checks all edges, closure, and the projected/singleton observations. This
generator and the Python file game are not trusted proof oracles.
"""
from collections import deque
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'src'))
from count import filegame

slots = filegame.chu_file_slots(0)
initial = tuple(s.start for s in slots)
states, parents, index = [initial], [None], {initial: 0}
queue = deque([initial])
while queue:
    st = queue.popleft()
    occ = {r for r in st if r > 0}
    for i, r in enumerate(st):
        if r <= 0:
            continue
        successors = [st[:i] + (0,) + st[i+1:]]
        for dest in filegame._dests(slots[i], r, occ, 12):
            successors.append(st[:i] + (dest,) + st[i+1:])
            if filegame.in_zone(slots[i].colour, r, 12, 4) or filegame.in_zone(slots[i].colour, dest, 12, 4):
                successors.append(st[:i] + (-1,) + st[i+1:])
        for nxt in successors:
            if nxt not in index:
                index[nxt] = len(states)
                states.append(nxt)
                parents.append(index[st])
                queue.append(nxt)

def encoded(st):
    return tuple(13 if r == -1 else r for r in st)

def literal(st):
    return '[' + ','.join(map(str, encoded(st))) + ']'

def tree(ids):
    if not ids:
        return '.empty', 'True.intro'
    mid = len(ids)//2
    i = ids[mid]
    left, lp = tree(ids[:mid])
    right, rp = tree(ids[mid+1:])
    return f'(.node {literal(states[i])} {left} {right})', f'⟨r{i}, {lp}, {rp}⟩'

directory = Path('out/lean-witnesses/ChuShogi/LanceCertificate')
directory.mkdir(parents=True, exist_ok=True)
header = "namespace ChuShogi.LanceCertificate\nopen FileGame FiniteSearch LanceObservables\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 2000000000\n\n"
last = 'ChuShogi.LanceObservables'
for start in range(0, len(states), 256):
    module = f'ChuShogi.LanceCertificate.Part{start//256:03}'
    path = Path('out/lean-witnesses') / (module.replace('.', '/') + '.lean')
    with path.open('w') as f:
        f.write(f'import {last}\n\n' + header)
        for i in range(start, min(start+256, len(states))):
            rhs = 'Reach.initial' if i == 0 else f'Reach.step r{parents[i]} (by decide)'
            f.write(f'theorem r{i} : R {literal(states[i])} := {rhs}\n')
        f.write('\nend ChuShogi.LanceCertificate\n')
    last = module

out = Path('out/lean-witnesses/ChuShogi/LanceCertificate.lean')
out.write_text("""import ChuShogi.LanceCachedCertificate

/-! Public lance-provider certificate. Regenerate from the repository root:
python3 lean/scripts/generate_lance_certificate.py
python3 lean/scripts/generate_lance_cached_certificate.py

Predecessor edges, stored state codes, complete graph closure and all queried
projections/singletons are ordinary kernel checked. No full promoted-family
classification theorem or native computation oracle is assumed. -/
namespace ChuShogi.LanceCertificate
export LanceCachedCertificate (reach_classified capture_reachable singleton_reachable projected_iff)
end ChuShogi.LanceCertificate
""")
print(f'Generated {len(states)} checked predecessor declarations and public certificate wrapper')
