import ChuShogi.IntegerCompletion
import ChuShogi.MemoizedSum

/-! A complete executable grouped counter with a cache of unrestricted
placement values. The finite query list is generated from every reduced row
and every admissible pawn total. It is not a user-supplied certificate. -/
namespace ChuShogi.EfficientCounter

def unrestricted (r : Bool) : List Nat → Nat :=
  let cs := FreeEGF.labelledCoefficients r
  fun xs => UnrestrictedEvaluation.fromCoefficients cs
    (72-xs[0]?.getD 0) (72-xs[1]?.getD 0) (xs[2]?.getD 0)

def rowQueries (e : List Nat × Nat) : List (List Nat × Nat) :=
  let j := e.1[0]?.getD 0
  let d0 := e.1[1]?.getD 0
  let d1 := e.1[2]?.getD 0
  let k := e.1[3]?.getD 0
  (List.range (j+1)).map fun t => ([d0,d1,t+k],e.2*(2^t*((t+k).factorial/t.factorial)))

def queries (raw : WeightedDP.Table (List Nat)) : List (List Nat × Nat) := raw.flatMap rowQueries

theorem row_correct (r : Bool) (e : List Nat × Nat) :
    MemoizedSum.reference (unrestricted r) (rowQueries e) = e.2*IntegerCompletion.finish r e.1 := by
  unfold MemoizedSum.reference rowQueries IntegerCompletion.finish IntegerCompletion.finishWith
  simp only [List.map_map,Function.comp_def]
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  simp only [unrestricted,UnrestrictedEvaluation.uu,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
  ring

theorem queries_correct (r : Bool) (raw : WeightedDP.Table (List Nat)) :
    MemoizedSum.reference (unrestricted r) (queries raw) =
      WeightedDP.integral raw (IntegerCompletion.finish r) := by
  induction raw with
  | nil => rfl
  | cons e raw ih =>
    change MemoizedSum.reference (unrestricted r) (rowQueries e++queries raw) = _
    simp only [MemoizedSum.reference,List.map_append,List.sum_append] at ih ⊢
    rw [← MemoizedSum.reference, row_correct, ih]
    rfl

def numerator (r : Bool) : Nat := MemoizedSum.evaluate (unrestricted r) (queries ReducedTables.table)
def count (r : Bool) : Nat := numerator r/64

theorem numerator_reference (r : Bool) : numerator r = IntegerCompletion.numerator r := by
  rw [numerator,MemoizedSum.evaluate_correct,queries_correct]
  rfl

theorem division_exact (r : Bool) : 64 ∣ numerator r := by
  rw [numerator_reference]
  exact IntegerCompletion.division_exact r

theorem count_correct (r : Bool) : count r = FiniteBoards.card (StructuralDecomposition.Stratum r) := by
  rw [count,numerator_reference]
  exact IntegerCompletion.count_correct r

theorem count_C_r : count true = FiniteBoards.card Specification.C_r := count_correct true
theorem count_C_nr : count false = FiniteBoards.card Specification.C_nr := count_correct false

end ChuShogi.EfficientCounter
