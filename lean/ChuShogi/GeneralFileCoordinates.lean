import ChuShogi.FileSuffixPlan

/-! Complete file coordinates for an arbitrary terminal weight. This permits
conditioning on a selected summary using the same checked interval recursion.
-/
namespace ChuShogi.GeneralFileCoordinates
open ConcreteDP FileBranchCoordinates

def count (finish : Summary → Nat) (p : Summary) (fs : List (List Local)) : Nat :=
  WeightedDP.integral (SummaryCode.groupTable fs) (fun s => finish (add p s))

theorem count_nil (finish : Summary → Nat) (p : Summary) : count finish p []=finish p := by
  simp [count,SummaryCode.groupTable,HashAggregation.dp,WeightedDP.integral,SummaryCode.decode_encode,add_zero]

theorem count_cons (finish : Summary → Nat) (p : Summary) (xs : List Local) (fs : List (List Local)) :
    count finish p (xs::fs)=(xs.map fun u => count finish (add p (CompactSummary.compactFeature u)) fs).sum := by
  simp only [count,SummaryCode.group_integral,WeightedDP.dp_integral,WeightedDP.tuples,
    List.map_flatMap,WeightedDP.sum_flatMap,List.map_map,Function.comp_def,WeightedDP.summary,add_swap]

def Code (finish : Summary → Nat) : List (List Local) → Summary → Type
  | [],p => Fin (finish p)
  | xs::fs,p => Σ i : Fin xs.length, Code finish fs (add p (CompactSummary.compactFeature xs[i.val]))

def equivalence (finish : Summary → Nat) : (fs : List (List Local)) → (p : Summary) → Fin (count finish p fs) ≃ Code finish fs p
  | [],p => finCongr (count_nil finish p)
  | xs::fs,p =>
    (finCongr (count_cons finish p xs fs)).trans
      ((LinearWeightedBranches.onList xs _).trans (Equiv.sigmaCongrRight fun i =>
        equivalence finish fs (add p (CompactSummary.compactFeature xs[i.val]))))

def tuple (finish : Summary → Nat) : (fs : List (List Local)) → (p : Summary) → Code finish fs p → List Local
  | [],_,_ => []
  | xs::fs,p,x => xs[x.1.val]::tuple finish fs (add p (CompactSummary.compactFeature xs[x.1.val])) x.2

def finalSummary (finish : Summary → Nat) : (fs : List (List Local)) → (p : Summary) → Code finish fs p → Summary
  | [],p,_ => p
  | xs::fs,p,x => finalSummary finish fs (add p (CompactSummary.compactFeature xs[x.1.val])) x.2

def leaf (finish : Summary → Nat) : (fs : List (List Local)) → (p : Summary) → (x : Code finish fs p) → Fin (finish (finalSummary finish fs p x))
  | [],_,x => x
  | xs::fs,p,x => leaf finish fs (add p (CompactSummary.compactFeature xs[x.1.val])) x.2

theorem tuple_mem (finish : Summary → Nat) (fs : List (List Local)) (p : Summary) (x : Code finish fs p) :
    tuple finish fs p x∈WeightedDP.tuples fs := by
  induction fs generalizing p with
  | nil => simp [tuple,WeightedDP.tuples]
  | cons xs fs ih =>
    exact List.mem_flatMap.mpr ⟨xs[x.1.val],List.getElem_mem x.1.isLt,
      List.mem_map.mpr ⟨tuple finish fs _ x.2,ih _ x.2,rfl⟩⟩

theorem final_summary (finish : Summary → Nat) (fs : List (List Local)) (p : Summary) (x : Code finish fs p) :
    finalSummary finish fs p x=add p (CompactSummary.compactSummary (tuple finish fs p x)) := by
  induction fs generalizing p with
  | nil => exact (add_zero p).symm
  | cons xs fs ih =>
    change finalSummary finish fs _ x.2=_
    rw [ih]
    exact (add_swap p _ _).symm

theorem coordinates_injective (finish : Summary → Nat) (fs : List (List Local))
    (hn : ∀ xs∈fs, xs.Nodup) (p : Summary) (x y : Code finish fs p)
    (ht : tuple finish fs p x=tuple finish fs p y) (hi : (leaf finish fs p x).val=(leaf finish fs p y).val) : x=y := by
  induction fs generalizing p with
  | nil => exact Fin.ext hi
  | cons xs fs ih =>
    rcases x with ⟨i,x⟩
    rcases y with ⟨j,y⟩
    have he := List.cons.inj ht
    have hij : i=j := Fin.ext ((List.Nodup.getElem_inj (hn xs (by simp))).mp he.1)
    subst j
    have htail : x=y := ih (fun ys hy => hn ys (by simp [hy])) _ x y he.2 hi
    subst y
    rfl

end ChuShogi.GeneralFileCoordinates
