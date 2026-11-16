import ChuShogi

/-! A realized summary smoke execution, not certification of paper integers. -/
namespace ChuShogi.EvaluatorCheck
open Specification Promotion ConcreteDP

def emptyTuple : List Local := indices.map fun x => (x,List.replicate (labels x).length 0)
def emptySummary : Summary := ⟨0,0,12,12,12,0,0,2,2,2,2,2,2⟩

theorem zero_bounded (ss : List OrderedFile.Slot) :
    OrderedFile.Bounded ss (List.replicate ss.length 0) := by
  induction ss with
  | nil => rfl
  | cons s ss ih => exact ⟨0,_,rfl,Or.inl rfl,ih⟩

theorem zero_ordered (n : Nat) : OrderedFile.Ordered (List.replicate n 0) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨fun _ _ => Or.inl rfl,ih⟩

theorem empty_valid : ConcreteDP.Valid emptyTuple := by
  have h (xs : List (Fin 12)) : WeightedDP.Valid (xs.map LocalAdmissible)
      (xs.map fun x => (x,List.replicate (labels x).length 0)) := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      refine ⟨_,_,rfl,⟨rfl,?_,zero_ordered _⟩,ih⟩
      simpa only [List.length_map] using zero_bounded ((labels x).map orderedLabel)
  exact h indices
theorem empty_summary : CompactSummary.compactSummary emptyTuple = emptySummary := by decide
theorem empty_realized : CompactSummary.RealizedCompact emptySummary := ⟨emptyTuple,empty_valid,empty_summary⟩

#eval let q := CompletionCoefficients.evaluate true emptySummary; (q.den,q.num.toNat)
#eval let q := CompletionCoefficients.evaluate false emptySummary; (q.den,q.num.toNat)
#print axioms empty_realized

end ChuShogi.EvaluatorCheck
