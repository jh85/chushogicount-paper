import ChuShogi.ConfigurationSum

/-! Canonical group EGF sum identified with the already verified reference
weights, on every realizable full or compact summary. This is still symbolic;
the efficient coefficient factorization must replace the configuration sum.
-/
namespace ChuShogi.ConfigurationWeight
open Specification Promotion ConcreteDP BoardDecomposition SummaryBridge StructuralDecomposition
open GroupCoverage ConfigurationSum ResidualWords ResidualProfileCounts OccupancyBridge
open scoped Classical

theorem available_card (u : Board) (a : Nat) :
    Fintype.card (AvailableClass u a) = ResidualSquares.availableCount u a := by
  calc
    Fintype.card (AvailableClass u a) = Nat.card (AvailableClass u a) := Nat.card_eq_fintype_card.symm
    _ = (FiniteBoards.subtypeEnum squares (fun s => u s = none ∧ squareClass s = a)).length :=
      (square_filter_card _).symm
    _ = ResidualSquares.availableCount u a := by
      rw [FiniteBoards.subtypeEnum_length]
      unfold ResidualSquares.availableCount
      apply congrArg List.length
      apply List.filter_congr
      intro t _
      by_cases h : u t = none ∧ squareClass t = a <;> simp [h]

theorem class_size (a : Nat) (ha : a < 2) :
    (squares.filter fun s => decide (squareClass s = a)).length = 72 := by
  have he : a = 0 ∨ a = 1 := by omega
  rcases he with rfl | rfl <;> decide

theorem remaining_card (u : Board) (hu : OnlyConfined u) (h1 : I1 u) (a : Nat) (ha : a < 2) :
    Fintype.card (AvailableClass u a) = 72-occupiedField (boardSummary u) a := by
  rw [available_card]
  have h := ResidualSquares.partition_count u a
  rw [class_size a ha,← boardSummary_occupied u h1 hu a ha] at h
  omega

noncomputable def realizedFormula (r : Bool) (s : Summary) : ℚ :=
  if h : StructuralCount.Realized s then formula r s (sized_realized s h) (72-s.d0) (72-s.d1) else 0

noncomputable def compactFormula (r : Bool) (s : Summary) : ℚ :=
  if h : CompactSummary.RealizedCompact s then formula r s (sized_compact_realized s h) (72-s.d0) (72-s.d1) else 0

theorem profile_erase (r : Bool) (s : Summary) (n0 n1 : CompletionProfiles.Counts) :
    CompletionProfiles.ValidProfile r (CompactSummary.erase s) n0 n1 ↔
      CompletionProfiles.ValidProfile r s n0 n1 := by
  have hc (c : Colour) (k : Kind) : cap (CompactSummary.erase s) c k = cap s c k := by
    cases c <;> cases k <;> rfl
  simp only [CompletionProfiles.ValidProfile,CompletionProfiles.Conditions,hc]
  rfl

theorem formula_erase (r : Bool) (s : Summary) (hs : Sized s) (he : Sized (CompactSummary.erase s))
    (f0 f1 : Nat) : formula r (CompactSummary.erase s) he f0 f1 = formula r s hs f0 f1 := by
  have hc : Nat.card {w : (Fin f0 → Option Piece) × (Fin f1 → Option Piece) //
      CompletionProfiles.ValidProfile r (CompactSummary.erase s)
        (CanonicalWordProfiles.wordCounts w.1) (CanonicalWordProfiles.wordCounts w.2)} =
      Nat.card {w : (Fin f0 → Option Piece) × (Fin f1 → Option Piece) //
      CompletionProfiles.ValidProfile r s
        (CanonicalWordProfiles.wordCounts w.1) (CanonicalWordProfiles.wordCounts w.2)} :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (fun w => profile_erase r s _ _))
  have h0 := words_natcard_formula (S0 := Fin f0) (S1 := Fin f1) r s hs
  have h1 := words_natcard_formula (S0 := Fin f0) (S1 := Fin f1) r (CompactSummary.erase s) he
  simp only [Fintype.card_fin] at h0 h1
  rw [← h0,← h1]
  exact congrArg (fun n : Nat => (n : ℚ)) hc

/-- No application-specific completion or summary premise remains. -/
theorem realized_eq_weight (r : Bool) (s : Summary) :
    realizedFormula r s = (StructuralCount.weight r s : ℚ) := by
  by_cases h : StructuralCount.Realized s
  · simp only [realizedFormula,StructuralCount.weight,dite_eq_left h]
    let us := Classical.choose h
    have hv := renderAny_valid us (Classical.choose_spec h).1
    have he : boardSummary (renderAny us) = s :=
      (StructuralCount.summary_renderAny us (Classical.choose_spec h).1).trans (Classical.choose_spec h).2
    have hc := ConfigurationSum.completion_formula r (renderAny us) hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
    rw [remaining_card _ hv.1 hv.2.1 0 (by decide),remaining_card _ hv.1 hv.2.1 1 (by decide)] at hc
    simpa only [occupiedField,ite_eq_left rfl,show (1 : Nat) ≠ 0 by decide,ite_eq_right,ite_true,ite_false,he] using hc.symm
  · simp only [realizedFormula,StructuralCount.weight,dite_eq_right h,Nat.cast_zero]

theorem compact_eq_weight (r : Bool) (s : Summary) :
    compactFormula r s = (CompactSummary.compactWeight r s : ℚ) := by
  by_cases h : CompactSummary.RealizedCompact s
  · simp only [compactFormula,CompactSummary.compactWeight,dite_eq_left h]
    let us := Classical.choose h
    have hv := renderAny_valid us (Classical.choose_spec h).1
    have he : CompactSummary.erase (boardSummary (renderAny us)) = s := by
      rw [StructuralCount.summary_renderAny us (Classical.choose_spec h).1,
        ← CompactSummary.summary_compact]
      exact (Classical.choose_spec h).2
    have hc := ConfigurationSum.completion_formula r (renderAny us) hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
    rw [remaining_card _ hv.1 hv.2.1 0 (by decide),remaining_card _ hv.1 hv.2.1 1 (by decide)] at hc
    have hf := formula_erase r (boardSummary (renderAny us)) (sized_board _ hv.2.1)
      (sized_erase _ (sized_board _ hv.2.1)) (72-s.d0) (72-s.d1)
    simp only [he] at hf
    rw [hf]
    have he0 := congrArg Summary.d0 he
    have he1 := congrArg Summary.d1 he
    change (boardSummary (renderAny us)).d0 = s.d0 at he0
    change (boardSummary (renderAny us)).d1 = s.d1 at he1
    simpa only [occupiedField,ite_eq_left rfl,show (1 : Nat) ≠ 0 by decide,ite_eq_right,ite_true,ite_false,he0,he1] using hc.symm
  · simp only [compactFormula,CompactSummary.compactWeight,dite_eq_right h,Nat.cast_zero]

def integral (t : WeightedDP.Table Summary) (f : Summary → ℚ) : ℚ :=
  (t.map fun e => (e.2 : ℚ)*f e.1).sum

theorem cast_integral (t : WeightedDP.Table Summary) (f : Summary → Nat) :
    (WeightedDP.integral t f : ℚ) = integral t (fun s => (f s : ℚ)) := by
  induction t with
  | nil => rfl
  | cons e t ih =>
    simp only [WeightedDP.integral_cons,integral,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_mul] at ih ⊢
    rw [ih]

theorem realized_total (r : Bool) :
    integral table (realizedFormula r) = (FiniteBoards.card (StructuralDecomposition.Stratum r) : ℚ) := by
  have he : realizedFormula r = fun s => (StructuralCount.weight r s : ℚ) := funext (realized_eq_weight r)
  rw [he,← cast_integral]
  exact congrArg (fun n : Nat => (n : ℚ)) (StructuralCount.structural_count r)

theorem compact_total (r : Bool) :
    integral CompactSummary.compactTable (compactFormula r) =
      (FiniteBoards.card (StructuralDecomposition.Stratum r) : ℚ) := by
  have he : compactFormula r = fun s => (CompactSummary.compactWeight r s : ℚ) := funext (compact_eq_weight r)
  rw [he,← cast_integral]
  exact congrArg (fun n : Nat => (n : ℚ)) (CompactSummary.compact_count r)

theorem reference_profile_eq (r : Bool) (s : Summary) :
    compactFormula r s = (ProfileCount.compactProfileWeight r s : ℚ) := by
  rw [ProfileCount.compactProfileWeight_eq,compact_eq_weight]

theorem compact_C_r : integral CompactSummary.compactTable (compactFormula true) = (FiniteBoards.card C_r : ℚ) :=
  compact_total true

theorem compact_C_nr : integral CompactSummary.compactTable (compactFormula false) = (FiniteBoards.card C_nr : ℚ) :=
  compact_total false

end ChuShogi.ConfigurationWeight
