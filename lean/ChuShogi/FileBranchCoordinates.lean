import ChuShogi.LinearWeightedBranches
import ChuShogi.SummaryCode

/-! Executable file-branch interval coordinates, using complete compressed
suffix aggregation for every branch weight. A terminal coordinate is an index
of a completion, not yet an efficient decoding of that completion to a Board.
This keeps the remaining completion-indexing obligation explicit. -/
namespace ChuShogi.FileBranchCoordinates
open ConcreteDP

def terminal (r : Bool) (s : Summary) : Nat := EvaluatorRefinement.evaluateNat r s

def count (r : Bool) (accSummary : Summary) (fs : List (List Local)) : Nat :=
  WeightedDP.integral (SummaryCode.groupTable fs) (fun tail => terminal r (add accSummary tail))

theorem add_zero (s : Summary) : add s zero=s := by cases s; simp [ConcreteDP.add,zero]
theorem zero_add (s : Summary) : add zero s=s := by cases s; simp [ConcreteDP.add,zero]
theorem add_swap (p s u : Summary) : add p (add s u) = add (add p u) s := by
  rw [AggregationOrder.add_comm s u,← AggregationOrder.add_assoc]

theorem count_nil (r : Bool) (p : Summary) : count r p [] = terminal r p := by
  rw [count,SummaryCode.group_integral]
  simp [WeightedDP.dp,WeightedDP.integral,add_zero]

theorem count_cons (r : Bool) (p : Summary) (xs : List Local) (fs : List (List Local)) :
    count r p (xs::fs) = (xs.map fun u => count r (add p (CompactSummary.compactFeature u)) fs).sum := by
  simp only [count,SummaryCode.group_integral,WeightedDP.dp_integral,WeightedDP.tuples,
    List.map_flatMap,WeightedDP.sum_flatMap,List.map_map,Function.comp_def,WeightedDP.summary,add_swap]

theorem sum_get (xs : List A) (f : A → Nat) :
    (xs.map f).sum = ∑ i : Fin xs.length, f xs[i.val] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simpa only [List.map_cons,List.sum_cons,List.length_cons,Fin.sum_univ_succ,
      List.getElem_cons_zero,List.getElem_cons_succ,Fin.val_zero,Fin.val_succ] using
      congrArg (fun n => f x+n) ih

/-- Coordinates select one actual local entry per file, followed by a terminal
completion index. They never enumerate the product of all file entries. -/
def Code (r : Bool) : (fs : List (List Local)) → Summary → Type
  | [],p => Fin (terminal r p)
  | xs::fs,p => Σ i : Fin xs.length, Code r fs (add p (CompactSummary.compactFeature xs[i.val]))

def equivalence (r : Bool) : (fs : List (List Local)) → (p : Summary) → Fin (count r p fs) ≃ Code r fs p
  | [],p => finCongr (count_nil r p)
  | xs::fs,p =>
    (finCongr (count_cons r p xs fs)).trans
      ((LinearWeightedBranches.onList xs _).trans (Equiv.sigmaCongrRight fun i =>
        equivalence r fs (add p (CompactSummary.compactFeature xs[i.val]))))

def unrank (r : Bool) (fs : List (List Local)) (p : Summary) := (equivalence r fs p).toFun
def rank (r : Bool) (fs : List (List Local)) (p : Summary) := (equivalence r fs p).invFun

theorem rank_unrank (r : Bool) (fs : List (List Local)) (p : Summary) (i : Fin (count r p fs)) :
    rank r fs p (unrank r fs p i) = i := (equivalence r fs p).symm_apply_apply i

theorem unrank_rank (r : Bool) (fs : List (List Local)) (p : Summary) (x : Code r fs p) :
    unrank r fs p (rank r fs p x) = x := (equivalence r fs p).apply_symm_apply x

theorem root_count (r : Bool) : count r zero files = FiniteBoards.card (StructuralDecomposition.Stratum r) := by
  rw [count,SummaryCode.group_integral]
  simp only [zero_add]
  exact ExecutableCounter.count_compact r

theorem uniform_input (r : Bool) (fs : List (List Local)) (p : Summary)
    (d : PMF (Fin (count r p fs))) (h : ∀ i, d i = (count r p fs : ENNReal)⁻¹) (x : Code r fs p) :
    (d.map (unrank r fs p)) x = (count r p fs : ENNReal)⁻¹ :=
  MathSampling.uniform_equiv (equivalence r fs p) d _ h x

end ChuShogi.FileBranchCoordinates
