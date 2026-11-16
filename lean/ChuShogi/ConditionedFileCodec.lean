import ChuShogi.GeneralTupleCodec
import ChuShogi.SummaryArithmetic

/-! Select an actual tuple conditional on its summary. Every branch weight is
one lookup in a proved complete suffix index, rather than a suffix-table scan.
-/
namespace ChuShogi.ConditionedFileCodec
open ConcreteDP GeneralFileCoordinates FileBranchCoordinates FileSuffixPlan

def indicator (target s : Summary) : Nat := if s=target then 1 else 0

def fastCount {fs : List (List Local)} (plan : Plan fs) (target accSummary : Summary) : Nat :=
  if SummaryArithmetic.LE accSummary target then lookup plan (SummaryArithmetic.sub target accSummary) else 0

theorem fastCount_correct {fs : List (List Local)} (plan : Plan fs) (target accSummary : Summary) :
    fastCount plan target accSummary=GeneralFileCoordinates.count (indicator target) accSummary fs := by
  unfold GeneralFileCoordinates.count indicator fastCount
  simp only [SummaryArithmetic.add_eq_iff]
  by_cases h : SummaryArithmetic.LE accSummary target
  · simp only [h,true_and,ite_true]
    exact lookup_correct plan _
  · simp [h,WeightedDP.integral]

def coordinates {fs : List (List Local)} (plan : Plan fs) (target accSummary : Summary) :
    Fin (GeneralFileCoordinates.count (indicator target) accSummary fs) ≃ Code (indicator target) fs accSummary :=
  match fs,plan with
  | [],.nil => finCongr (GeneralFileCoordinates.count_nil _ _)
  | xs::fs,.cons _ _ tail _ => by
    let weight (u : Local) := fastCount tail target (add accSummary (CompactSummary.compactFeature u))
    have he : GeneralFileCoordinates.count (indicator target) accSummary (xs::fs)=(xs.map weight).sum := by
      rw [GeneralFileCoordinates.count_cons]
      apply congrArg List.sum
      apply List.map_congr_left
      intro u _
      exact (fastCount_correct tail target _).symm
    exact (finCongr he).trans ((LinearWeightedBranches.onList xs weight).trans
      (Equiv.sigmaCongrRight fun i : Fin xs.length =>
        (finCongr (fastCount_correct tail target _)).trans
          (coordinates tail target (add accSummary (CompactSummary.compactFeature xs[i.val])))))

def forgetLeaf (target accSummary : Summary) (fs : List (List Local)) :
    GeneralTupleCodec.Coordinates (indicator target) fs accSummary ≃
      {us : List Local // us∈WeightedDP.tuples fs ∧ add accSummary (CompactSummary.compactSummary us)=target} where
  toFun p := ⟨p.1.val,p.1.property,by
    have hi := p.2.isLt
    by_contra hn
    simp [indicator,hn] at hi⟩
  invFun us := ⟨⟨us.val,us.property.1⟩,⟨0,by simp [indicator,us.property.2]⟩⟩
  left_inv p := by
    rcases p with ⟨⟨us,hm⟩,⟨k,hk⟩⟩
    have hz : k=0 := by unfold indicator at hk; split at hk <;> omega
    subst k
    rfl
  right_inv _ := rfl

@[irreducible] def equivalence {fs : List (List Local)} (plan : Plan fs) (hn : ∀ xs∈fs, xs.Nodup) (target : Summary) :
    Fin (lookup plan target) ≃ {us : List Local // us∈WeightedDP.tuples fs ∧ CompactSummary.compactSummary us=target} := by
  have he : lookup plan target=GeneralFileCoordinates.count (indicator target) zero fs := by
    have h := fastCount_correct plan target zero
    simpa only [fastCount,SummaryArithmetic.zero_le,ite_true,SummaryArithmetic.sub_zero] using h
  let convert : {us : List Local // us∈WeightedDP.tuples fs ∧ add zero (CompactSummary.compactSummary us)=target} ≃
      {us : List Local // us∈WeightedDP.tuples fs ∧ CompactSummary.compactSummary us=target} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun _ => by rw [zero_add]; rfl)
  exact (finCongr he).trans ((coordinates plan target zero).trans
    ((GeneralTupleCodec.equivalence _ fs hn zero).trans ((forgetLeaf target zero fs).trans convert)))

end ChuShogi.ConditionedFileCodec
