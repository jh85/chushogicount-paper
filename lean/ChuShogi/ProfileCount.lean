import ChuShogi.ResidualProfileCounts
import ChuShogi.CompactSummary

/-! The concrete DP weights are identified with the derived multinomial profile
formula. Efficient group/EGF evaluation of these sums is a further refinement. -/
namespace ChuShogi.ProfileCount
open Specification ConcreteDP StructuralDecomposition StructuralCount FiniteBoards
open ResidualProfileCounts

open scoped Classical

noncomputable def profileWeight (r : Bool) (s : Summary) : Nat :=
  if h : Realized s then profileFormula r (renderAny (Classical.choose h)) else 0

theorem profileWeight_eq (r : Bool) (s : Summary) : profileWeight r s = weight r s := by
  by_cases h : Realized s
  · simp only [profileWeight,weight,dite_eq_left h]
    have hv := renderAny_valid _ (Classical.choose_spec h).1
    exact (completion_profile_formula r _ hv.1 hv.2.1 hv.2.2.1 hv.2.2.2).symm
  · simp only [profileWeight,weight,dite_eq_right h]

/-- Both independent Board strata are counted by the concrete DP with the
proved arithmetic-profile multinomial weights. No completion-cardinality
correctness hypothesis is supplied to this theorem. -/
theorem profile_total (r : Bool) : WeightedDP.integral table (profileWeight r) = card (Stratum r) := by
  have he : profileWeight r = weight r := funext (profileWeight_eq r)
  rw [he]
  exact structural_count r

noncomputable def compactProfileWeight (r : Bool) (s : Summary) : Nat :=
  if h : CompactSummary.RealizedCompact s then profileFormula r (renderAny (Classical.choose h)) else 0

theorem compactProfileWeight_eq (r : Bool) (s : Summary) :
    compactProfileWeight r s = CompactSummary.compactWeight r s := by
  by_cases h : CompactSummary.RealizedCompact s
  · simp only [compactProfileWeight,CompactSummary.compactWeight,dite_eq_left h]
    have hv := renderAny_valid _ (Classical.choose_spec h).1
    exact (completion_profile_formula r _ hv.1 hv.2.1 hv.2.2.1 hv.2.2.2).symm
  · simp only [compactProfileWeight,CompactSummary.compactWeight,dite_eq_right h]

/-- The same concrete profile formula verifies the default stats=False summary. -/
theorem compact_profile_total (r : Bool) :
    WeightedDP.integral CompactSummary.compactTable (compactProfileWeight r) = card (Stratum r) := by
  have he : compactProfileWeight r = CompactSummary.compactWeight r := funext (compactProfileWeight_eq r)
  rw [he]
  exact CompactSummary.compact_count r

theorem profile_C_r : WeightedDP.integral table (profileWeight true) = card C_r := profile_total true
theorem profile_C_nr : WeightedDP.integral table (profileWeight false) = card C_nr := profile_total false

end ChuShogi.ProfileCount
