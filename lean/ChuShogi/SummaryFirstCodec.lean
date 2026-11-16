import ChuShogi.ConditionedFileCodec
import ChuShogi.SuffixSupport
import ChuShogi.FiniteFibrePartition

/-! Summary-first tuple/terminal indexing. Complete DP multiplicity selects a
summary, then conditioned suffix lookups select its tuple, then its completion
index. Equal summaries never identify distinct confined placements. -/
namespace ChuShogi.SummaryFirstCodec
open ConcreteDP FileSuffixPlan SuffixSupport

abbrev Tuples (fs : List (List Local)) := {us : List Local // us∈WeightedDP.tuples fs}

def size (finish : Summary → Nat) {fs : List (List Local)} (plan : Plan fs) : Nat :=
  LinearWeightedBranches.total ((summaries plan).map fun s => lookup plan s*finish s)

theorem size_integral (finish : Summary → Nat) {fs : List (List Local)} (plan : Plan fs) :
    size finish plan=WeightedDP.integral (rows plan) (fun k => finish (SummaryCode.decode k)) := by
  rw [← active_integral plan]
  unfold size
  rw [LinearWeightedBranches.total_eq_sum]
  unfold summaries WeightedDP.integral
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  simp only [Function.comp_def,active_lookup plan e he]

def liftFibre (fs : List (List Local)) (s : Summary) :
    {us : List Local // us∈WeightedDP.tuples fs ∧ CompactSummary.compactSummary us=s} ≃
      {us : Tuples fs // CompactSummary.compactSummary us.val=s} where
  toFun p := ⟨⟨p.val,p.property.1⟩,p.property.2⟩
  invFun p := ⟨p.val.val,p.val.property,p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[irreducible] def equivalence (finish : Summary → Nat) {fs : List (List Local)}
    (plan : Plan fs) (hn : ∀ xs∈fs, xs.Nodup) :
    Fin (size finish plan) ≃ Σ us : Tuples fs, Fin (finish (CompactSummary.compactSummary us.val)) := by
  let keys := summaries plan
  let stat (us : Tuples fs) := CompactSummary.compactSummary us.val
  let w (s : Summary) := lookup plan s*finish s
  let branches : (Σ i : Fin keys.length, Fin (w keys[i.val])) ≃ FiniteFibrePartition.Data keys stat finish :=
    Equiv.sigmaCongrRight (fun i : Fin keys.length =>
      finProdFinEquiv.symm.trans (Equiv.prodCongr
        ((ConditionedFileCodec.equivalence plan hn keys[i.val]).trans (liftFibre fs keys[i.val])) (Equiv.refl _)))
  exact (finCongr (LinearWeightedBranches.total_eq_sum (keys.map w))).trans
    ((LinearWeightedBranches.onList keys w).trans (branches.trans
    (FiniteFibrePartition.equivalence keys (summaries_nodup plan) stat finish
      (fun us => summaries_complete plan us.val us.property))))

end ChuShogi.SummaryFirstCodec
