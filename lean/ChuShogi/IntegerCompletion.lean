import ChuShogi.PawnDiagonal
import ChuShogi.UnrestrictedEvaluation
import ChuShogi.ReducedTables

/-! Integer `tok`/`uu` completion formula and exact final division. None of the
runtime path enumerates the independent universe of Boards. -/
namespace ChuShogi.IntegerCompletion
open EGFConvolution CoefficientEquivalence ReducedGeometry

def finishWith (u : Nat → Nat → Nat → Nat) (xs : List Nat) : Nat :=
  let j := xs[0]?.getD 0
  let d0 := xs[1]?.getD 0
  let d1 := xs[2]?.getD 0
  let k := xs[3]?.getD 0
  ((List.range (j+1)).map fun t => 2^t*((t+k).factorial/t.factorial)*u d0 d1 (t+k)).sum

def finish (r : Bool) (xs : List Nat) : Nat := finishWith (UnrestrictedEvaluation.uu r) xs

theorem finish_correct (r : Bool) (xs : List Nat) :
    (finish r xs : ℚ) = ReducedGeometry.finish r xs := by
  let j := xs[0]?.getD 0
  let d0 := xs[1]?.getD 0
  let d1 := xs[2]?.getD 0
  let k := xs[3]?.getD 0
  change ((((List.range (j+1)).map fun t => 2^t*((t+k).factorial/t.factorial)*
    UnrestrictedEvaluation.uu r d0 d1 (t+k)).sum : Nat) : ℚ) = _
  rw [ReducedGeometry.finish,integral_convolve,integral_exchange,PawnDiagonal.pawn_integral]
  simp only [Nat.cast_list_sum,List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  simp only [Nat.cast_mul,EGFArithmetic.factorial_ratio t (t+k) (by omega),degree_add_assoc,ScaledPolynomials.lift_add]
  have he := UnrestrictedEvaluation.uu_scaling r d0 d1 (t+k)
  change ((2^t : Nat) : ℚ)*(((t+k).factorial : ℚ)/(t.factorial : ℚ))*
      (UnrestrictedEvaluation.uu r d0 d1 (t+k) : ℚ) =
    ((2^t : Nat) : ℚ)/(t.factorial : ℚ)*_
  rw [← he]
  ring

def numerator (r : Bool) : Nat := WeightedDP.integral ReducedTables.table (finish r)
def count (r : Bool) : Nat := numerator r/64

theorem numerator_correct (r : Bool) :
    (numerator r : ℚ) = 64*(FiniteBoards.card (StructuralDecomposition.Stratum r) : ℚ) := by
  rw [numerator,← RationalTable.integral_cast]
  simp_rw [finish_correct]
  exact ReducedTables.scaled_total r

theorem division_exact (r : Bool) : 64 ∣ numerator r :=
  (EGFArithmetic.final_division _ _ _ (by decide) (numerator_correct r)).1

theorem count_correct (r : Bool) : count r = FiniteBoards.card (StructuralDecomposition.Stratum r) :=
  (EGFArithmetic.final_division _ _ _ (by decide) (numerator_correct r)).2

theorem count_C_r : count true = FiniteBoards.card Specification.C_r := count_correct true
theorem count_C_nr : count false = FiniteBoards.card Specification.C_nr := count_correct false

end ChuShogi.IntegerCompletion
