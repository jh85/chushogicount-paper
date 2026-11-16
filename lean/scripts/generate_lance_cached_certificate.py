#!/usr/bin/env python3
"""Generate numeric-key lance graph certificates, reusing checked predecessor proofs.

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

def key(st):
    out = 0
    for r in encoded(st):
        out = 14*out+r
    return out

nodes=[]
def literal_tree(ids):
    if not ids:
        return '.empty', 'True.intro'
    mid=len(ids)//2; i=ids[mid]
    left,lp=literal_tree(ids[:mid]); right,rp=literal_tree(ids[mid+1:])
    return f'(.node {key(states[i])} {literal(states[i])} {left} {right})', f'⟨LanceCertificate.r{i}, {lp}, {rp}⟩'

def segmented(ids):
    if len(ids)<=128:
        term,proof=literal_tree(ids)
        name=f'tree{len(nodes)}'; nodes.append((name,term,proof,None)); return name
    mid=len(ids)//2; i=ids[mid]
    left=segmented(ids[:mid]); right=segmented(ids[mid+1:])
    name=f'tree{len(nodes)}'
    term=f'(.node {key(states[i])} {literal(states[i])} {left} {right})'
    proof=f'⟨LanceCertificate.r{i}, {left}_reachable, {right}_reachable⟩'
    nodes.append((name,term,proof,(i,left,right))); return name

root=segmented(sorted(range(len(states)),key=lambda i:key(states[i])))
header="namespace ChuShogi.LanceCachedCertificate\nopen FileGame FiniteSearch LanceObservables\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 2000000000\nset_option Elab.async false\n\n"
aliases="abbrev Tree := LanceStateCode.Tree\nabbrev All := LanceStateCode.All\nabbrev Correct := LanceStateCode.Correct\nabbrev contains := LanceStateCode.contains\n"
Path('out/lean-witnesses/ChuShogi').mkdir(parents=True, exist_ok=True)
with Path('out/lean-witnesses/ChuShogi/LanceCachedData.lean').open('w') as f:
    f.write('import ChuShogi.LanceCertificate.Part096\nimport ChuShogi.LanceStateCode\n\n/-! Generated numeric-key data; each predecessor, stored code, state shape\nand necessary classifier is checked by ordinary kernel proofs. -/\n'+header+aliases)
    for name,term,proof,children in nodes:
        f.write(f'def {name} : Tree := {term}\n')
        f.write(f'theorem {name}_reachable : All R {name} := {proof}\n')
        if children:
            _,left,right=children
            pc=f'⟨by decide, {left}_classified, {right}_classified⟩'
            pk=f'⟨by decide, by decide, {left}_correct, {right}_correct⟩'
        else:pc=pk='by decide'
        f.write(f'theorem {name}_classified : All (Classified slots) {name} := {pc}\n')
        f.write(f'theorem {name}_correct : Correct {name} := {pk}\n')
    f.write(f'def tree : Tree := {root}\n')
    for suffix,typ in [('reachable','All R'),('classified','All (Classified slots)'),('correct','Correct')]:
        f.write(f'theorem tree_{suffix} : {typ} tree := {root}_{suffix}\n')
    f.write('end ChuShogi.LanceCachedCertificate\n')

with Path('out/lean-witnesses/ChuShogi/LanceCachedCertificate.lean').open('w') as f:
    f.write('import ChuShogi.LanceCachedData\n\n/-! Complete graph closure and exactly the provider observations required\nby the counter. Numeric lookup is justified by checked keys and injectivity. -/\n'+header)
    for name,_,_,children in nodes:
        if children:
            _,left,right=children
            pc=f'⟨by decide, {left}_closed, {right}_closed⟩'
        else:pc='by decide'
        f.write(f'theorem {name}_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) {name} := {pc}\n')
    f.write(f'theorem tree_closed : All (fun s => (next slots s).all (fun t => contains (code t) tree) = true) tree := {root}_closed\n')
    f.write("""
theorem initial_contained : contains (code initial) tree = true := by decide

theorem reach_classified (st : State) (h : R st) : Classified slots st :=
  LanceStateCode.contains_all _ tree tree_correct tree_classified st
    (LanceStateCode.reach_length _ _ _ h)
    (LanceStateCode.reach_contained slots initial rfl tree tree_correct initial_contained tree_closed st h)

theorem captured_checked : (OrderedFile.enumerate 0 OrderedFile.lanceSlots).all
    (fun u => contains (code (capture u)) tree) = true := by decide

theorem captured_contained : ∀ u ∈ OrderedFile.enumerate 0 OrderedFile.lanceSlots,
    contains (code (capture u)) tree = true := List.all_eq_true.mp captured_checked

theorem singleton_checked : (OrderedFile.enumerate 0 OrderedFile.lanceSlots).all
    (fun u => (List.finRange 6).all (fun i => if decide (eligible u i) then contains (code (mark u i)) tree else true)) = true := by decide

theorem singleton_contained : ∀ u ∈ OrderedFile.enumerate 0 OrderedFile.lanceSlots,
    ∀ i : Fin 6, eligible u i → contains (code (mark u i)) tree = true := by
  intro u hu i hi
  have h := (List.all_eq_true.mp ((List.all_eq_true.mp singleton_checked) u hu)) i (List.mem_finRange i)
  simpa only [decide_eq_true hi,ite_true] using h

theorem capture_reachable (u : List Nat) (h : valid u) : R (capture u) :=
  LanceStateCode.contains_all _ tree tree_correct tree_reachable _
    (LanceStateCode.capture_length u h) (captured_contained u ((valid_mem u).mp h))

theorem singleton_reachable (u : List Nat) (h : valid u) (i : Fin 6) (hi : eligible u i) : R (mark u i) :=
  LanceStateCode.contains_all _ tree tree_correct tree_reachable _
    (LanceStateCode.mark_length u h i) (singleton_contained u ((valid_mem u).mp h) i hi)

theorem projected_iff (u : List Nat) : (∃ st, R st ∧ st.map shown=u) ↔ valid u := by
  constructor
  · rintro ⟨st,hs,rfl⟩
    simpa only [valid,← slots_ordered] using (reach_classified st hs).2.1
  · intro hu
    exact ⟨capture u,capture_reachable u hu,capture_projection u hu⟩

end ChuShogi.LanceCachedCertificate
""")
print(f'Generated cached data and full closure/observable checker for {len(states)} states')
