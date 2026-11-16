import ChuShogi.TwoClassCanonicalCodec

/-! Transport Fin-indexed bound placements to the actual canonical labels.
Bound symbols are transported bijectively; unrestricted role counts are fixed.
-/
namespace ChuShogi.BoundLabelRelabelling
open CanonicalAlphabet BoundPlacements
variable {X Y X0 X1 Y0 Y1 : Type}
variable [DecidableEq X] [DecidableEq Y] [DecidableEq X0] [DecidableEq X1] [DecidableEq Y0] [DecidableEq Y1]

def alphabet (e : X ≃ Y) : Option (X ⊕ Unbound) ≃ Option (Y ⊕ Unbound) :=
  Equiv.optionCongr (Equiv.sumCongr e (Equiv.refl Unbound))

def wordEquivalence (e : X ≃ Y) (n : Nat) :
    (Fin n → Option (X ⊕ Unbound)) ≃ (Fin n → Option (Y ⊕ Unbound)) :=
  Equiv.arrowCongr (Equiv.refl _) (alphabet e)

theorem bound_multiplicity (e : X ≃ Y) (w : Fin n → Option (X ⊕ Unbound)) (y : Y) :
    MultinomialPlacements.multiplicity (wordEquivalence e n w) (some (.inl y)) =
      MultinomialPlacements.multiplicity w (some (.inl (e.symm y))) := by
  change MultinomialPlacements.multiplicity (fun i => alphabet e (w i)) (some (.inl y)) = _
  exact CanonicalUnrestrictedCodec.multiplicity_relabel w (alphabet e) (some (.inl y))

theorem unbound_multiplicity (e : X ≃ Y) (w : Fin n → Option (X ⊕ Unbound)) (r : Unbound) :
    MultinomialPlacements.multiplicity (wordEquivalence e n w) (some (.inr r)) =
      MultinomialPlacements.multiplicity w (some (.inr r)) := by
  change MultinomialPlacements.multiplicity (fun i => alphabet e (w i)) (some (.inr r)) = _
  exact CanonicalUnrestrictedCodec.multiplicity_relabel w (alphabet e) (some (.inr r))

theorem good_transport (e : X ≃ Y) (w : Fin n → Option (X ⊕ Unbound)) :
    Good w ↔ Good (wordEquivalence e n w) := by
  rw [good_iff_counts,good_iff_counts]
  constructor
  · intro h y
    rw [bound_multiplicity]
    exact h (e.symm y)
  · intro h x
    have hy := h (e x)
    rw [bound_multiplicity,Equiv.symm_apply_apply] at hy
    exact hy

def pairEquivalence (e0 : X0 ≃ Y0) (e1 : X1 ≃ Y1) (n0 n1 : Nat) :
    (Fin n0 → Option (X0 ⊕ Unbound)) × (Fin n1 → Option (X1 ⊕ Unbound)) ≃
      (Fin n0 → Option (Y0 ⊕ Unbound)) × (Fin n1 → Option (Y1 ⊕ Unbound)) :=
  Equiv.prodCongr (wordEquivalence e0 n0) (wordEquivalence e1 n1)

def equivalence (e0 : X0 ≃ Y0) (e1 : X1 ≃ Y1) (n0 n1 : Nat) (counts : Unbound → Nat) :
    {w : (Fin n0 → Option (X0 ⊕ Unbound)) × (Fin n1 → Option (X1 ⊕ Unbound)) //
      TwoClassEGF.GoodPair w ∧ TwoClassEGF.Counts counts w} ≃
      {w : (Fin n0 → Option (Y0 ⊕ Unbound)) × (Fin n1 → Option (Y1 ⊕ Unbound)) //
        TwoClassEGF.GoodPair w ∧ TwoClassEGF.Counts counts w} :=
  Equiv.subtypeEquiv (pairEquivalence e0 e1 n0 n1) (fun w => by
    change (Good w.1 ∧ Good w.2) ∧ TwoClassEGF.Counts counts w ↔
      (Good (wordEquivalence e0 n0 w.1) ∧ Good (wordEquivalence e1 n1 w.2)) ∧
        (∀ r, MultinomialPlacements.multiplicity (wordEquivalence e0 n0 w.1) (some (.inr r))+
          MultinomialPlacements.multiplicity (wordEquivalence e1 n1 w.2) (some (.inr r))=counts r)
    rw [← good_transport,← good_transport]
    simp only [TwoClassEGF.Counts,unbound_multiplicity])

end ChuShogi.BoundLabelRelabelling
