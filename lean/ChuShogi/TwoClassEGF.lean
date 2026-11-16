module
public import ChuShogi.BoundWordCounts

@[expose] public section

/-! Two-class bound selections and unrestricted placements, before specializing
the role alphabet to the concrete canonical Board inventory. -/
namespace ChuShogi.TwoClassEGF
open scoped Classical
open BoundPlacements MultinomialPlacements UnrestrictedWords EGFArithmetic

variable {X0 X1 S0 S1 R : Type}
variable [Fintype X0] [Fintype X1] [Fintype S0] [Fintype S1] [Fintype R]
variable [DecidableEq X0] [DecidableEq X1] [DecidableEq R]

abbrev Words := (S0 → Option (X0 ⊕ R)) × (S1 → Option (X1 ⊕ R))
abbrev Embeddings := (X0 ↪ S0) × (X1 ↪ S1)
abbrev ResidualWords (e : Embeddings (X0 := X0) (X1 := X1) (S0 := S0) (S1 := S1)) :=
  (Residual e.1 → Option R) × (Residual e.2 → Option R)

def GoodPair (f : Words (X0 := X0) (X1 := X1) (S0 := S0) (S1 := S1) (R := R)) : Prop :=
  Good f.1 ∧ Good f.2

def Counts (n : R → Nat) (f : Words (X0 := X0) (X1 := X1) (S0 := S0) (S1 := S1) (R := R)) : Prop :=
  ∀ r, multiplicity f.1 (some (.inr r))+multiplicity f.2 (some (.inr r))=n r

def ResidualCounts (n : R → Nat) (e : Embeddings (X0 := X0) (X1 := X1) (S0 := S0) (S1 := S1)) (w : ResidualWords (R := R) e) : Prop :=
  ∀ r, multiplicity w.1 (some r)+multiplicity w.2 (some r)=n r

noncomputable def baseEquivalence :
    (Σ e : Embeddings (X0 := X0) (X1 := X1) (S0 := S0) (S1 := S1), ResidualWords (R := R) e) ≃
      {f : Words (X0 := X0) (X1 := X1) (S0 := S0) (S1 := S1) (R := R) // GoodPair f} := by
  let split : (Σ e : Embeddings (X0 := X0) (X1 := X1) (S0 := S0) (S1 := S1), ResidualWords (R := R) e) ≃
      (Σ e0 : X0 ↪ S0, Residual e0 → Option R) × (Σ e1 : X1 ↪ S1, Residual e1 → Option R) := {
    toFun := fun p => (⟨p.1.1,p.2.1⟩,⟨p.1.2,p.2.2⟩)
    invFun := fun p => ⟨(p.1.1,p.2.1),(p.1.2,p.2.2)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let flat : {f0 : S0 → Option (X0 ⊕ R) // Good f0} ×
      {f1 : S1 → Option (X1 ⊕ R) // Good f1} ≃
      {f : Words (X0 := X0) (X1 := X1) (S0 := S0) (S1 := S1) (R := R) // GoodPair f} := {
    toFun := fun f => ⟨(f.1.val,f.2.val),f.1.property,f.2.property⟩
    invFun := fun f => (⟨f.val.1,f.property.1⟩,⟨f.val.2,f.property.2⟩)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact split.trans ((Equiv.prodCongr equivalence equivalence).trans flat)

noncomputable def countedEquivalence (n : R → Nat) :
    (Σ e : Embeddings (X0 := X0) (X1 := X1) (S0 := S0) (S1 := S1), {w : ResidualWords (R := R) e // ResidualCounts n e w}) ≃
      {f : Words (X0 := X0) (X1 := X1) (S0 := S0) (S1 := S1) (R := R) // GoodPair f ∧ Counts n f} := by
  let split : (Σ e : Embeddings (X0 := X0) (X1 := X1) (S0 := S0) (S1 := S1), {w : ResidualWords (R := R) e // ResidualCounts n e w}) ≃
      {p : Σ e : Embeddings (X0 := X0) (X1 := X1) (S0 := S0) (S1 := S1), ResidualWords (R := R) e // ResidualCounts n p.1 p.2} := {
    toFun := fun p => ⟨⟨p.1,p.2.val⟩,p.2.property⟩
    invFun := fun p => ⟨p.val.1,⟨p.val.2,p.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let ref : {p : Σ e : Embeddings (X0 := X0) (X1 := X1) (S0 := S0) (S1 := S1), ResidualWords (R := R) e // ResidualCounts n p.1 p.2} ≃
      {f : {f : Words (X0 := X0) (X1 := X1) (S0 := S0) (S1 := S1) (R := R) // GoodPair f} // Counts n f.val} :=
    Equiv.subtypeEquiv baseEquivalence (fun p => by
      change ResidualCounts n p.1 p.2 ↔ Counts n (assemble p.1.1 p.2.1,assemble p.1.2 p.2.2)
      simp only [ResidualCounts,Counts,unbound_multiplicity])
  exact split.trans (ref.trans (Equiv.subtypeSubtypeEquivSubtypeInter
    (GoodPair (X0 := X0) (X1 := X1) (S0 := S0) (S1 := S1) (R := R)) (Counts n)))

/-- Complete two-class EGF placement formula for distinct bound labels and
canonical unrestricted roles. Every unrestricted class split is included. -/
theorem count_egf (n : R → Nat) :
    (Fintype.card {f : Words (X0 := X0) (X1 := X1) (S0 := S0) (S1 := S1) (R := R) // GoodPair f ∧ Counts n f} : ℚ) =
      ((Fintype.card S0).descFactorial (Fintype.card X0) : ℚ)*
      ((Fintype.card S1).descFactorial (Fintype.card X1) : ℚ)*
      (((Fintype.card S0-Fintype.card X0)+(Fintype.card S1-Fintype.card X1)).descFactorial
        (∑ r, n r) : ℚ)*inverseFactorials n := by
  rw [← Fintype.card_congr (countedEquivalence n),Fintype.card_sigma,Nat.cast_sum]
  have he (e : Embeddings (X0 := X0) (X1 := X1) (S0 := S0) (S1 := S1)) :
      (Fintype.card {w : ResidualWords (R := R) e // ResidualCounts n e w} : ℚ) =
        (((Fintype.card S0-Fintype.card X0)+(Fintype.card S1-Fintype.card X1)).descFactorial
          (∑ r, n r) : ℚ)*inverseFactorials n := by
    have hc : Fintype.card {w : ResidualWords (R := R) e // ResidualCounts n e w} =
        Fintype.card {w : (Residual e.1 → Option R) × (Residual e.2 → Option R) //
          ∀ r, multiplicity w.1 (some r)+multiplicity w.2 (some r)=n r} :=
      Fintype.card_congr (Equiv.refl _)
    rw [hc,two_class_some_counts_egf,residual_card,residual_card]
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,
    Fintype.card_embedding_eq,Fintype.card_embedding_eq,Nat.cast_mul]
  ring

end ChuShogi.TwoClassEGF
