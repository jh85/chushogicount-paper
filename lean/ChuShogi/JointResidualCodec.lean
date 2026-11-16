import ChuShogi.ResidualFinCodec

/-! One canonical unrestricted multiset is placed across both residual square
classes. Class splits are decoded by an explicit domain equivalence, rather
than treating alternative splits or origin assignments as extra Boards. -/
namespace ChuShogi.JointResidualCodec
open BoundPlacements CanonicalAlphabet UnrestrictedWords

def splitFunction {S0 S1 T : Type} (e : S0 ⊕ S1 ≃ T) (A : Type) :
    (T → A) ≃ (S0 → A) × (S1 → A) :=
  (Equiv.arrowCongr e.symm (Equiv.refl A)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

theorem join_split {S0 S1 T A : Type} (e : S0 ⊕ S1 ≃ T) (w : T → Option A) :
    joinWords (splitFunction e (Option A) w) = fun s => w (e s) := by
  funext s
  cases s <;> rfl

def domainEquivalence (e0 : Fin k0 ↪ Fin n0) (e1 : Fin k1 ↪ Fin n1) :
    Residual e0 ⊕ Residual e1 ≃ Fin ((n0-k0)+(n1-k1)) :=
  (Equiv.sumCongr (ResidualFinCodec.equivalence e0).symm (ResidualFinCodec.equivalence e1).symm).trans finSumFinEquiv

theorem counts_transport (e0 : Fin k0 ↪ Fin n0) (e1 : Fin k1 ↪ Fin n1) (counts : Unbound → Nat)
    (w : Fin ((n0-k0)+(n1-k1)) → Option Unbound) :
    SomeCounts counts w ↔ TwoClassEGF.ResidualCounts counts (e0,e1)
      (splitFunction (domainEquivalence e0 e1) (Option Unbound) w) := by
  have hm (r : Unbound) : MultinomialPlacements.multiplicity w (some r) =
      MultinomialPlacements.multiplicity (splitFunction (domainEquivalence e0 e1) (Option Unbound) w).1 (some r)+
      MultinomialPlacements.multiplicity (splitFunction (domainEquivalence e0 e1) (Option Unbound) w).2 (some r) := by
    have h1 := ResidualFinCodec.multiplicity_domain (domainEquivalence e0 e1).symm w (some r)
    have h2 := join_multiplicity (splitFunction (domainEquivalence e0 e1) (Option Unbound) w) r
    rw [join_split] at h2
    exact h1.symm.trans h2
  simp only [SomeCounts,TwoClassEGF.ResidualCounts,hm]

def wordEquivalence (e0 : Fin k0 ↪ Fin n0) (e1 : Fin k1 ↪ Fin n1) (counts : Unbound → Nat) :
    {w : Fin ((n0-k0)+(n1-k1)) → Option Unbound // SomeCounts counts w} ≃
      {w : (Residual e0 → Option Unbound) × (Residual e1 → Option Unbound) //
        TwoClassEGF.ResidualCounts counts (e0,e1) w} :=
  Equiv.subtypeEquiv (splitFunction (domainEquivalence e0 e1) (Option Unbound))
    (counts_transport e0 e1 counts)

def equivalence (e0 : Fin k0 ↪ Fin n0) (e1 : Fin k1 ↪ Fin n1) (counts : Unbound → Nat) :
    Fin (CanonicalUnrestrictedCodec.size ((n0-k0)+(n1-k1)) counts) ≃
      {w : (Residual e0 → Option Unbound) × (Residual e1 → Option Unbound) //
        TwoClassEGF.ResidualCounts counts (e0,e1) w} :=
  (CanonicalUnrestrictedCodec.equivalence _ counts).trans (wordEquivalence e0 e1 counts)

end ChuShogi.JointResidualCodec
