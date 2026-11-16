import ChuShogi.CanonicalWordProfiles
import ChuShogi.FiniteConfigurations

/-! Reindex the proved completion words by their unique canonical group state.
The configuration universe remains symbolic; executable coefficient convolution
is a further factorization of this sum. -/
namespace ChuShogi.ConfigurationSum
open Specification Promotion CompletionProfiles ConcreteDP GroupCoverage GroupConfigurations
open CanonicalAlphabet CanonicalWordProfiles FiniteConfigurations EGFArithmetic
open scoped Classical

variable {S0 S1 : Type} [Fintype S0] [Fintype S1]

private theorem card_instances (A : Type) (i j : Fintype A) :
    @Fintype.card A i = @Fintype.card A j := @Fintype.card_congr A A i j (Equiv.refl A)

noncomputable def wordEquivalence (r : Bool) (s : Summary) (hs : Sized s) :
    (Σ g : Config r s, {w : (S0 → Option Piece) × (S1 → Option Piece) //
      Represents g (wordCounts w.1) (wordCounts w.2)}) ≃
    {w : (S0 → Option Piece) × (S1 → Option Piece) //
      ValidProfile r s (wordCounts w.1) (wordCounts w.2)} :=
  Equiv.ofBijective (fun p => ⟨p.2.val,(grouped_iff r s hs _ _).mp
    (represents_grouped p.1 _ _ p.2.property)⟩) (by
      constructor
      · rintro ⟨g,⟨w,hw⟩⟩ ⟨g',⟨w',hw'⟩⟩ he
        have hwEq : w = w' := congrArg Subtype.val he
        subst w'
        have hg : g = g' := represents_unique g g' _ _ hw hw'
        subst g'
        rfl
      · intro w
        obtain ⟨g,hg,_⟩ := (valid_unique s hs r _ _).mp w.property
        exact ⟨⟨g,⟨w.val,hg⟩⟩,rfl⟩)

noncomputable def term (f0 f1 : Nat) (g : Config r s) : ℚ :=
  (f0.descFactorial (Fintype.card (Bound0 g)) : ℚ)*
  (f1.descFactorial (Fintype.card (Bound1 g)) : ℚ)*
  (((f0-Fintype.card (Bound0 g))+(f1-Fintype.card (Bound1 g))).descFactorial
    (∑ p, unboundCounts g p) : ℚ)*inverseFactorials (unboundCounts g)

noncomputable def formula (r : Bool) (s : Summary) (hs : Sized s) (f0 f1 : Nat) : ℚ :=
  letI := configFintype s hs r
  ∑ g : Config r s, term f0 f1 g

/-- Complete reindexing, including empty fibres, with no assumed enumeration or
placement-correctness hypothesis. -/
theorem words_formula (r : Bool) (s : Summary) (hs : Sized s) :
    (Fintype.card {w : (S0 → Option Piece) × (S1 → Option Piece) //
      ValidProfile r s (wordCounts w.1) (wordCounts w.2)} : ℚ) =
      formula r s hs (Fintype.card S0) (Fintype.card S1) := by
  let := configFintype s hs r
  rw [← Fintype.card_congr (wordEquivalence r s hs),Fintype.card_sigma,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro g _
  exact fibre_egf g

theorem words_natcard_formula (r : Bool) (s : Summary) (hs : Sized s) :
    (Nat.card {w : (S0 → Option Piece) × (S1 → Option Piece) //
      ValidProfile r s (wordCounts w.1) (wordCounts w.2)} : ℚ) =
      formula r s hs (Fintype.card S0) (Fintype.card S1) := by
  rw [Nat.card_eq_fintype_card]
  exact words_formula r s hs

/-- The actual completion cardinality is now expressed by canonical group
weights and the EGF placement factors. This sum itself is a symbolic reference. -/
theorem completion_formula (r : Bool) (u : Board) (hu : BoardDecomposition.OnlyConfined u)
    (h1 : I1 u) (h2 : I2 u) (h3 : I3 u) :
    (FiniteBoards.card (SummarySufficiency.StratumCompletes r u) : ℚ) =
      formula r (SummaryBridge.boardSummary u) (sized_board u h1)
        (Fintype.card (ResidualWords.AvailableClass u 0)) (Fintype.card (ResidualWords.AvailableClass u 1)) := by
  rw [ResidualProfileCounts.board_card]
  let e := ResidualProfileCounts.completionWordIso r u hu h1 h2 h3
  let eqv := Equiv.mk e.forward e.backward e.left_inverse e.right_inverse
  rw [← Nat.card_congr eqv,Nat.card_eq_fintype_card]
  have he : Fintype.card {w : ResidualWords.Words u //
      ResidualProfileCounts.WordConditions r (SummaryBridge.boardSummary u)
        (MultinomialPlacements.multiplicity w.1) (MultinomialPlacements.multiplicity w.2)} =
      Fintype.card {w : (ResidualWords.AvailableClass u 0 → Option Piece) ×
        (ResidualWords.AvailableClass u 1 → Option Piece) //
          ValidProfile r (SummaryBridge.boardSummary u) (wordCounts w.1) (wordCounts w.2)} :=
    Fintype.card_congr (Equiv.refl _)
  rw [he]
  convert (words_formula (S0 := ResidualWords.AvailableClass u 0)
    (S1 := ResidualWords.AvailableClass u 1) r (SummaryBridge.boardSummary u) (sized_board u h1)) using 1
  apply congrArg (fun n : Nat => (n : ℚ))
  exact card_instances _ _ _

end ChuShogi.ConfigurationSum
