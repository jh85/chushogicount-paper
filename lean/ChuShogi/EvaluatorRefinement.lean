import ChuShogi.UnboundInventory

/-! The efficient compressed coefficient/placement evaluator computes the
independent completion cardinality. No Board or configuration universe occurs
in the executable path; the finite universes below are used only for proofs. -/
namespace ChuShogi.EvaluatorRefinement
open Specification Promotion ConcreteDP GroupCoverage GroupConfigurations FiniteConfigurations
open CanonicalAlphabet UnboundInventory CompletionCoefficients ConfigurationSum

theorem term_refinement (f0 f1 : Nat) (g : Config r s) :
    EGFConvolution.tupleWeight ((inputs g).map FreeEGF.term)*
      placement f0 f1 (EGFConvolution.tupleDegree ((inputs g).map FreeEGF.term)) =
        ConfigurationSum.term f0 f1 g := by
  rw [weight_factorials]
  unfold placement ConfigurationSum.term
  rw [degree_a0,degree_a1,degree_m]
  rw [← EGFArithmetic.rational_falling_remainders]
  ring

/-- The whole efficient polynomial/placement evaluation is a refinement of the
proved complete canonical configuration sum, for every sized summary. -/
theorem evaluate_formula (r : Bool) (s : Summary) (hs : Sized s) :
    evaluate r s = formula r s hs (72-s.d0) (72-s.d1) := by
  let := configFintype s hs r
  unfold evaluate
  rw [coefficients_canonical r s hs]
  apply Finset.sum_congr rfl
  intro g _
  exact term_refinement _ _ g

theorem evaluate_weight (r : Bool) (s : Summary) (h : StructuralCount.Realized s) :
    evaluate r s = (StructuralCount.weight r s : ℚ) := by
  rw [evaluate_formula r s (sized_realized s h)]
  have he := ConfigurationWeight.realized_eq_weight r s
  simpa only [ConfigurationWeight.realizedFormula,dite_eq_left h] using he

theorem evaluate_compact_weight (r : Bool) (s : Summary) (h : CompactSummary.RealizedCompact s) :
    evaluate r s = (CompactSummary.compactWeight r s : ℚ) := by
  rw [evaluate_formula r s (sized_compact_realized s h)]
  have he := ConfigurationWeight.compact_eq_weight r s
  simpa only [ConfigurationWeight.compactFormula,dite_eq_left h] using he

theorem evaluate_profile (r : Bool) (s : Summary) (h : CompactSummary.RealizedCompact s) :
    evaluate r s = (ProfileCount.compactProfileWeight r s : ℚ) := by
  rw [ProfileCount.compactProfileWeight_eq,evaluate_compact_weight r s h]

/-- Conversion is justified on the actual DP domain by the proved cardinality
identity, not by assuming intermediate EGF coefficients are integers. -/
def evaluateNat (r : Bool) (s : Summary) : Nat := (evaluate r s).num.toNat

theorem evaluateNat_weight (r : Bool) (s : Summary) (h : StructuralCount.Realized s) :
    evaluateNat r s = StructuralCount.weight r s := by
  unfold evaluateNat
  rw [evaluate_weight r s h]
  simp

theorem evaluateNat_compact_weight (r : Bool) (s : Summary) (h : CompactSummary.RealizedCompact s) :
    evaluateNat r s = CompactSummary.compactWeight r s := by
  unfold evaluateNat
  rw [evaluate_compact_weight r s h]
  simp

theorem evaluate_integral (r : Bool) (s : Summary) (h : CompactSummary.RealizedCompact s) :
    ∃ n : Nat, evaluate r s = n := ⟨_,evaluate_compact_weight r s h⟩

end ChuShogi.EvaluatorRefinement
