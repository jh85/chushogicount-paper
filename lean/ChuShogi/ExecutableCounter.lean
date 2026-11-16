import ChuShogi.EvaluatorRefinement

/-! Executable compressed completion weights applied to the concrete full and
compact DPs. These are ordinary kernel correctness theorems, distinct from
certifying a particular execution or refining the faster special-file grouping.
-/
namespace ChuShogi.ExecutableCounter
open Specification ConcreteDP EvaluatorRefinement StructuralDecomposition

/-- Construct the completion function once, retaining the summary-independent
free table in its closure rather than recomputing it at every DP entry. -/
def cachedEvaluator (r : Bool) : Summary → Nat :=
  let free := FreeEGF.coefficients r
  fun s => (EGFConvolution.integral
    (EGFConvolution.convolve free (PromotedCoordinates.coefficients s))
    (CompletionCoefficients.placement (72-s.d0) (72-s.d1))).num.toNat

theorem cachedEvaluator_eq (r : Bool) (s : Summary) : cachedEvaluator r s = evaluateNat r s := rfl

def countFull (r : Bool) : Nat := WeightedDP.integral table (cachedEvaluator r)
def countCompact (r : Bool) : Nat := WeightedDP.integral CompactSummary.compactTable (cachedEvaluator r)

theorem full_reference (r : Bool) : countFull r = StructuralCount.structuralCount r := by
  unfold countFull StructuralCount.structuralCount
  rw [concrete_dp_integral,concrete_dp_integral]
  apply congrArg List.sum
  apply List.map_congr_left
  intro us hu
  exact evaluateNat_weight r (summary us) ⟨us,(StructuralCount.tuple_mem_iff us).mp hu,rfl⟩

theorem compact_reference (r : Bool) : countCompact r = CompactSummary.compactCount r := by
  unfold countCompact CompactSummary.compactCount CompactSummary.compactTable
  rw [WeightedDP.dp_integral,WeightedDP.dp_integral]
  apply congrArg List.sum
  apply List.map_congr_left
  intro us hu
  exact evaluateNat_compact_weight r (CompactSummary.compactSummary us) ⟨us,(StructuralCount.tuple_mem_iff us).mp hu,rfl⟩

/-- The executable Lean counter counts exactly independent I1--I9 Boards in
each royal stratum. No source-table, numerical or assumed formula premise. -/
theorem count_full (r : Bool) : countFull r = FiniteBoards.card (Stratum r) :=
  (full_reference r).trans (StructuralCount.structural_count r)

theorem count_compact (r : Bool) : countCompact r = FiniteBoards.card (Stratum r) :=
  (compact_reference r).trans (CompactSummary.compact_count r)

theorem count_C_r : countCompact true = FiniteBoards.card C_r := count_compact true
theorem count_C_nr : countCompact false = FiniteBoards.card C_nr := count_compact false

end ChuShogi.ExecutableCounter
