import ChuShogi.FiniteLookup
import ChuShogi.ResidualFinCodec

/-! Computable bound-label assembly and extraction, refining the existing
independent bound-word bijection. All searches range over the actual finite
labels/squares; canonical labels are not promotion-origin witnesses. -/
namespace ChuShogi.ComputedBoundWords
open BoundPlacements ResidualFinCodec
variable {R : Type} [DecidableEq R]

def origin (e : Fin k ↪ Fin n) (s : Fin n) (h : s ∈ Set.range e) : {i : Fin k // e i=s} :=
  let found := FiniteLookup.findValue (List.finRange k) (fun i => decide (e i=s)) (by
    obtain ⟨i,hi⟩ := h
    exact ⟨i,List.mem_finRange i,decide_eq_true hi⟩)
  ⟨found.val,of_decide_eq_true found.property⟩

def assemble (e : Fin k ↪ Fin n) (w : Residual e → Option R) (s : Fin n) : Option (Fin k ⊕ R) :=
  if h : s ∈ Set.range e then some (.inl (origin e s h).val)
  else (w ⟨s,h⟩).map Sum.inr

omit [DecidableEq R] in
theorem assemble_eq (e : Fin k ↪ Fin n) (w : Residual e → Option R) :
    assemble e w = BoundPlacements.assemble e w := by
  classical
  funext s
  by_cases h : s ∈ Set.range e
  · simp only [assemble,BoundPlacements.assemble,dite_eq_left h]
    congr 2
    apply e.injective
    exact (origin e s h).property.trans (Classical.choose_spec h).symm
  · simp only [assemble,BoundPlacements.assemble,dite_eq_right h]

omit [DecidableEq R] in
theorem assemble_good (e : Fin k ↪ Fin n) (w : Residual e → Option R) : Good (assemble e w) := by
  rw [assemble_eq]
  exact BoundPlacements.assemble_good e w

def position (f : Fin n → Option (Fin k ⊕ R)) (h : Good f) (x : Fin k) :
    {s : Fin n // f s=some (.inl x)} :=
  let found := FiniteLookup.findValue (List.finRange n) (fun s => decide (f s=some (.inl x))) (by
    obtain ⟨s,hs,_⟩ := h x
    exact ⟨s,List.mem_finRange s,decide_eq_true hs⟩)
  ⟨found.val,of_decide_eq_true found.property⟩

def embedding (f : Fin n → Option (Fin k ⊕ R)) (h : Good f) : Fin k ↪ Fin n where
  toFun x := (position f h x).val
  inj' := by
    intro x y he
    change (position f h x).val=(position f h y).val at he
    have hx := (position f h x).property
    have hy := (position f h y).property
    rw [he] at hx
    exact Sum.inl.inj (Option.some.inj (hx.symm.trans hy))

theorem embedding_eq (f : Fin n → Option (Fin k ⊕ R)) (h : Good f) :
    embedding f h = BoundPlacements.embedding f h := by
  classical
  apply Function.Embedding.ext
  intro x
  exact (Classical.choose_spec (h x)).2 _ (position f h x).property

def forward (p : Σ e : Fin k ↪ Fin n, Residual e → Option R) :
    {f : Fin n → Option (Fin k ⊕ R) // Good f} := ⟨assemble p.1 p.2,assemble_good p.1 p.2⟩

def backward (f : {f : Fin n → Option (Fin k ⊕ R) // Good f}) :
    Σ e : Fin k ↪ Fin n, Residual e → Option R :=
  ⟨embedding f.val f.property,residualWord f.val (embedding f.val f.property)⟩

omit [DecidableEq R] in
theorem forward_eq (p : Σ e : Fin k ↪ Fin n, Residual e → Option R) :
    forward p = BoundPlacements.equivalence p := Subtype.ext (assemble_eq p.1 p.2)

theorem forward_backward (f : {f : Fin n → Option (Fin k ⊕ R) // Good f}) :
    forward (backward f)=f := by
  apply Subtype.ext
  change assemble (embedding f.val f.property) (residualWord f.val (embedding f.val f.property)) = f.val
  rw [assemble_eq,embedding_eq,assemble_extract]

theorem backward_eq (f : {f : Fin n → Option (Fin k ⊕ R) // Good f}) :
    backward f = BoundPlacements.equivalence.symm f := by
  apply BoundPlacements.equivalence.injective
  rw [← forward_eq,forward_backward,Equiv.apply_symm_apply]

def equivalence : (Σ e : Fin k ↪ Fin n, Residual e → Option R) ≃
    {f : Fin n → Option (Fin k ⊕ R) // Good f} where
  toFun := forward
  invFun := backward
  left_inv p := by rw [backward_eq,forward_eq,Equiv.symm_apply_apply]
  right_inv := forward_backward

end ChuShogi.ComputedBoundWords
