import ChuShogi.WordIndexing

/-! Mixed-radix indexing of injections: distinct canonical bound labels select
different squares. Removing the selected square leaves the same smaller
problem, with no enumeration of all injections or labelled promotion origins. -/
namespace ChuShogi.InjectionIndexing

def lower (p j : Fin (n+1)) (h : j ≠ p) : Fin n :=
  Fin.insertNth (α := fun q => q ≠ p → Fin n) p
    (fun h => False.elim (h rfl)) (fun i _ => i) j h

theorem lower_succAbove (p : Fin (n+1)) (i : Fin n) :
    lower p (p.succAbove i) (Fin.succAbove_ne p i) = i := by simp [lower]

def removeEquivalence (p : Fin (n+1)) : {j : Fin (n+1) // j ≠ p} ≃ Fin n where
  toFun j := lower p j.val j.property
  invFun i := ⟨p.succAbove i,Fin.succAbove_ne p i⟩
  left_inv := by
    rintro ⟨j,h⟩
    apply Subtype.ext
    revert h
    refine Fin.succAboveCases p ?_ (fun i => ?_) j
    · intro h; exact False.elim (h rfl)
    · intro h
      change p.succAbove (lower p (p.succAbove i) h) = p.succAbove i
      rw [lower_succAbove]
  right_inv := lower_succAbove p

def join (p : Fin (n+1)) (tail : Fin k ↪ Fin n) : Fin (k+1) ↪ Fin (n+1) where
  toFun := Fin.cons p (fun i => p.succAbove (tail i))
  inj' := by
    intro i j h
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j => exact False.elim ((Fin.succAbove_ne p (tail j)) h.symm)
    | succ i =>
      cases j using Fin.cases with
      | zero => exact False.elim ((Fin.succAbove_ne p (tail i)) h)
      | succ j => exact congrArg Fin.succ (tail.injective (Fin.succAbove_right_injective h))

def headTailEquivalence : (Fin (k+1) ↪ Fin (n+1)) ≃ (Fin (n+1) × (Fin k ↪ Fin n)) where
  toFun e := (e 0,{
    toFun := fun i => removeEquivalence (e 0) ⟨e i.succ,by
      intro h; exact Fin.succ_ne_zero i (e.injective h)⟩
    inj' := by
      intro i j h
      have he := (removeEquivalence (e 0)).injective h
      exact Fin.succ_injective _ (e.injective (congrArg Subtype.val he)) })
  invFun p := join p.1 p.2
  left_inv := by
    intro e
    apply Function.Embedding.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrArg Subtype.val ((removeEquivalence (e 0)).symm_apply_apply _)
  right_inv := by
    rintro ⟨p,tail⟩
    apply Prod.ext
    · rfl
    · apply Function.Embedding.ext
      intro i
      exact (removeEquivalence p).apply_symm_apply (tail i)

def emptyEquivalence (n : Nat) : Fin (n.descFactorial 0) ≃ (Fin 0 ↪ Fin n) where
  toFun _ := ⟨Fin.elim0,fun i => Fin.elim0 i⟩
  invFun _ := ⟨0,by simp⟩
  left_inv i := Fin.ext (by
    change 0=i.val
    have h := i.isLt
    have hz : n.descFactorial 0=1 := rfl
    omega)
  right_inv e := Function.Embedding.ext (fun i => Fin.elim0 i)

def impossibleEquivalence (k : Nat) : Fin (Nat.descFactorial 0 (k+1)) ≃ (Fin (k+1) ↪ Fin 0) where
  toFun i := Fin.elim0 (Fin.cast (Nat.zero_descFactorial_succ k) i)
  invFun e := Fin.elim0 (e 0)
  left_inv i := Fin.elim0 (Fin.cast (Nat.zero_descFactorial_succ k) i)
  right_inv e := Fin.elim0 (e 0)

def equivalence : (k n : Nat) → Fin (n.descFactorial k) ≃ (Fin k ↪ Fin n)
  | 0,n => emptyEquivalence n
  | k+1,0 => impossibleEquivalence k
  | k+1,n+1 => (finCongr (Nat.succ_descFactorial_succ n k)).trans
    (finProdFinEquiv.symm.trans ((Equiv.prodCongr (Equiv.refl _) (equivalence k n)).trans headTailEquivalence.symm))

def unrank (k n : Nat) := (equivalence k n).toFun
def rank (k n : Nat) := (equivalence k n).invFun

theorem rank_unrank (k n : Nat) (i : Fin (n.descFactorial k)) : rank k n (unrank k n i) = i :=
  (equivalence k n).symm_apply_apply i

theorem unrank_rank (k n : Nat) (e : Fin k ↪ Fin n) : unrank k n (rank k n e) = e :=
  (equivalence k n).apply_symm_apply e

theorem uniform_input (k n : Nat) (p : PMF (Fin (n.descFactorial k)))
    (h : ∀ i, p i = (n.descFactorial k : ENNReal)⁻¹) (e : Fin k ↪ Fin n) :
    (p.map (unrank k n)) e = (n.descFactorial k : ENNReal)⁻¹ :=
  MathSampling.uniform_equiv (equivalence k n) p _ h e

end ChuShogi.InjectionIndexing
