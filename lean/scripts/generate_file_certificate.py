#!/usr/bin/env python3
"""Generate proof terms, not trusted proof results, from the original file game.

Run from the repository root. Lean checks every predecessor step and independently
checks closure/classification. The Python source and generator are outside the
proof trust boundary. No counter source is changed.
"""
from collections import deque
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'src'))
from count import filegame

slots = filegame.chu_file_slots(3)
initial = tuple(s.start for s in slots)
states = [initial]
index = {initial: 0}
parents = [None]
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

ordered = sorted(range(len(states)), key=lambda i: encoded(states[i]))

def tree(ids):
    if not ids:
        return '.empty', 'True.intro'
    mid = len(ids)//2
    i = ids[mid]
    left, lp = tree(ids[:mid])
    right, rp = tree(ids[mid+1:])
    return f'(.node {literal(states[i])} {left} {right})', f'⟨r{i}, {lp}, {rp}⟩'

t, proof = tree(ordered)
out = Path('out/lean-witnesses/ChuShogi/GoBetweenCertificate.lean')
out.parent.mkdir(parents=True, exist_ok=True)
with out.open('w') as f:
    f.write('''import ChuShogi.FileGame

/-! Generated predecessor certificate. Regenerate with
`python3 lean/scripts/generate_file_certificate.py` from the repository root.
Every step below is an ordinary kernel-checked proof of the Lean transition.
The generator is not a proof oracle. -/
namespace ChuShogi.GoBetweenCertificate
open FileGame FiniteSearch
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

abbrev R := Reach (next goBetweenSlots) goBetweenInitial

''')
    for i, st in enumerate(states):
        rhs = 'Reach.initial' if i == 0 else f'Reach.step r{parents[i]} (by decide)'
        f.write(f'private theorem r{i} : R {literal(st)} := {rhs}\n')
    f.write(f'\ndef tree : Tree := {t}\n')
    f.write(f'\ntheorem tree_reachable : All R tree := {proof}\n')
    f.write('''
theorem tree_classified : All (Classified goBetweenSlots) tree := by decide

theorem tree_closed :
    All (fun s => (next goBetweenSlots s).all (fun t => contains t tree) = true) tree := by decide

theorem initial_contained : contains goBetweenInitial tree = true := by decide

theorem classified_contained (st : State) (h : Classified goBetweenSlots st) :
    contains st tree = true := by
  have checked : ∀ a b c d : Fin 14,
      Classified goBetweenSlots [a,b,c,d] → contains [a,b,c,d] tree = true := by decide
  have hl : st.length = 4 := h.1
  have he := List.eq_getElem_of_length_eq_four st hl
  rw [he] at h ⊢
  exact checked _ _ _ _ h

/-- Full soundness and completeness for the independent strengthened conditions. -/
theorem reach_iff (st : State) : R st ↔ Classified goBetweenSlots st := by
  constructor
  · intro hr
    exact contains_all _ tree tree_classified st
      (reach_contained goBetweenSlots goBetweenInitial tree initial_contained tree_closed st hr)
  · intro hc
    exact contains_all _ tree tree_reachable st (classified_contained st hc)

def states : List State := listing tree

theorem states_length : states.length = 844 := by decide

theorem tree_bounded : BoundedTree 0 (14^4) tree := by decide

theorem states_nodup : states.Nodup := bounded_nodup tree 0 (14^4) tree_bounded

theorem states_iff (st : State) : st ∈ states ↔ R st := by
  constructor
  · exact listing_all R tree tree_reachable st
  · intro h
    exact contains_mem tree st
      (reach_contained goBetweenSlots goBetweenInitial tree initial_contained tree_closed st h)

end ChuShogi.GoBetweenCertificate
''')
print(f'Generated {len(states)} checked-step declarations in {out}')
