module
public import ChuShogi.BoundPlacements
public import ChuShogi.UnrestrictedWords

@[expose] public section

/-! Counted refinement of bound-role removal. The constraints are on the word,
independently of the injection/residual-word representation. -/
namespace ChuShogi.BoundWordCounts
open scoped Classical
open BoundPlacements MultinomialPlacements UnrestrictedWords EGFArithmetic

variable {X S R : Type} [Fintype X] [Fintype S] [Fintype R] [DecidableEq X] [DecidableEq R]

def Conditions (n : R → Nat) (f : S → Option (X ⊕ R)) : Prop :=
  Good f ∧ ∀ r, multiplicity f (some (.inr r)) = n r

noncomputable def countedEquivalence (n : R → Nat) :
    (Σ e : X ↪ S, {w : Residual e → Option R // SomeCounts n w}) ≃
      {f : S → Option (X ⊕ R) // Conditions n f} := by
  let split : (Σ e : X ↪ S, {w : Residual e → Option R // SomeCounts n w}) ≃
      {p : Σ e : X ↪ S, Residual e → Option R // SomeCounts n p.2} := {
    toFun := fun p => ⟨⟨p.1,p.2.val⟩,p.2.property⟩
    invFun := fun p => ⟨p.val.1,⟨p.val.2,p.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let ref : {p : Σ e : X ↪ S, Residual e → Option R // SomeCounts n p.2} ≃
      {f : {f : S → Option (X ⊕ R) // Good f} //
        ∀ r, multiplicity f.val (some (.inr r)) = n r} :=
    Equiv.subtypeEquiv equivalence (fun p => by
      change SomeCounts n p.2 ↔ ∀ r, multiplicity (assemble p.1 p.2) (some (.inr r)) = n r
      simp only [SomeCounts,unbound_multiplicity])
  exact split.trans (ref.trans (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun f : S → Option (X ⊕ R) => Good f)
    (fun f : S → Option (X ⊕ R) => ∀ r, multiplicity f (some (.inr r)) = n r)))

/-- Distinct bound labels use a falling factorial. The remaining canonical
roles use the exact unrestricted EGF weight, with all empty squares included. -/
theorem count_egf (n : R → Nat) :
    (Fintype.card {f : S → Option (X ⊕ R) // Conditions n f} : ℚ) =
      ((Fintype.card S).descFactorial (Fintype.card X) : ℚ) *
      ((Fintype.card S-Fintype.card X).descFactorial (∑ r, n r) : ℚ)*inverseFactorials n := by
  rw [← Fintype.card_congr (countedEquivalence n),Fintype.card_sigma,Nat.cast_sum]
  have he (e : X ↪ S) :
      (Fintype.card {w : Residual e → Option R // SomeCounts n w} : ℚ) =
        ((Fintype.card S-Fintype.card X).descFactorial (∑ r, n r) : ℚ)*inverseFactorials n := by
    rw [some_counts_egf,residual_card]
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_embedding_eq]
  ring

end ChuShogi.BoundWordCounts
