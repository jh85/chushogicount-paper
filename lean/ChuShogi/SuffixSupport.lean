import ChuShogi.FileSuffixPlan

/-! Exact support and multiplicities of retained suffix tables. Positive rows
are canonical encoded summaries; arbitrary absent keys have weight zero. -/
namespace ChuShogi.SuffixSupport
open ConcreteDP WeightedDP FileSuffixPlan

theorem reference_expansion (fs : List (List Local)) (f : List Nat → Nat) :
    integral (reference fs) f=((tuples fs).map fun us => f (SummaryCode.encode (CompactSummary.compactSummary us))).sum := by
  rw [reference,HashAggregation.dp_integral,DPRenaming.dp_integral_map zero add SummaryCode.merge
    CompactSummary.compactFeature SummaryCode.encode SummaryCode.encode_add,dp_integral]
  rfl

theorem convolve_lookup_mem (a b : Table (List Nat)) (e : List Nat × Nat)
    (he : e∈HashAggregation.convolve SummaryCode.merge a b) :
    WeightedDP.lookup (HashAggregation.convolve SummaryCode.merge a b) e.1=e.2 := by
  let m : Std.HashMap (List Nat) Nat := a.foldl
    (fun m e => b.foldl (fun m v => HashAggregation.add m (SummaryCode.merge e.1 v.1) (e.2*v.2)) m) ∅
  change e∈m.toList at he
  change WeightedDP.lookup m.toList e.1=e.2
  rw [HashAggregation.lookup_toList,Std.HashMap.mem_toList_iff_getElem?_eq_some.mp he]
  rfl

theorem reference_lookup_mem (fs : List (List Local)) (e : List Nat × Nat) (he : e∈reference fs) :
    WeightedDP.lookup (reference fs) e.1=e.2 := by
  cases fs with
  | nil => simp only [reference,HashAggregation.dp,List.mem_singleton] at he; subst e; simp [reference,HashAggregation.dp,WeightedDP.lookup]
  | cons xs fs => exact convolve_lookup_mem _ _ e he

theorem reference_keys_nodup (fs : List (List Local)) : ((reference fs).map Prod.fst).Nodup := by
  cases fs with
  | nil => simp [reference,HashAggregation.dp]
  | cons xs fs =>
    unfold reference HashAggregation.dp HashAggregation.convolve
    rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
    apply List.Pairwise.imp _ Std.HashMap.distinct_keys_toList
    intro a b h he
    rw [he] at h
    simp at h

theorem positive_canonical (fs : List (List Local)) (e : List Nat × Nat) (he : e∈reference fs) (hn : 0<e.2) :
    SummaryCode.encode (SummaryCode.decode e.1)=e.1 := by
  by_contra h
  have hne (us : List Local) : SummaryCode.encode (CompactSummary.compactSummary us)≠e.1 := by
    intro he
    have hh := congrArg SummaryCode.decode he
    rw [SummaryCode.decode_encode] at hh
    exact h (by rw [← hh,he])
  have hz : WeightedDP.lookup (reference fs) e.1=0 := by
    rw [WeightedDP.lookup,reference_expansion]
    simp [hne]
  rw [reference_lookup_mem fs e he] at hz
  omega

def active {fs : List (List Local)} (p : Plan fs) : Rows := (rows p).filter fun e => decide (0<e.2)
def summaries {fs : List (List Local)} (p : Plan fs) : List Summary := (active p).map fun e => SummaryCode.decode e.1

theorem active_canonical {fs : List (List Local)} (p : Plan fs) (e : List Nat × Nat) (he : e∈active p) :
    SummaryCode.encode (SummaryCode.decode e.1)=e.1 := by
  have hh := List.mem_filter.mp he
  exact positive_canonical fs e (by simpa only [rows_correct] using hh.1) (of_decide_eq_true hh.2)

theorem active_lookup {fs : List (List Local)} (p : Plan fs) (e : List Nat × Nat) (he : e∈active p) :
    FileSuffixPlan.lookup p (SummaryCode.decode e.1)=e.2 := by
  rw [FileSuffixPlan.lookup_correct]
  rw [SummaryCode.groupTable,SummaryCode.integral_decode]
  change integral (reference fs) (fun k => if SummaryCode.decode k=SummaryCode.decode e.1 then 1 else 0)=e.2
  rw [reference_expansion]
  have hk := active_canonical p e he
  have hh : (fun us => if CompactSummary.compactSummary us=SummaryCode.decode e.1 then 1 else 0)=
      (fun us => if SummaryCode.encode (CompactSummary.compactSummary us)=e.1 then 1 else 0) := by
    funext us
    have heq : SummaryCode.encode (CompactSummary.compactSummary us)=e.1 ↔
        CompactSummary.compactSummary us=SummaryCode.decode e.1 := by
      constructor
      · intro h; simpa only [SummaryCode.decode_encode] using congrArg SummaryCode.decode h
      · intro h; exact (congrArg SummaryCode.encode h).trans hk
    simp only [heq]
  simp only [SummaryCode.decode_encode]
  rw [hh]
  exact (reference_expansion fs (fun k => if k=e.1 then 1 else 0)).symm.trans
    (reference_lookup_mem fs e (by rw [← rows_correct p]; exact (List.mem_filter.mp he).1))

theorem summaries_nodup {fs : List (List Local)} (p : Plan fs) : (summaries p).Nodup := by
  have hr : (rows p).Nodup := by
    rw [rows_correct]
    exact (reference_keys_nodup fs).of_map
  apply List.Nodup.map_on _ (hr.filter _)
  intro a ha b hb he
  have hk : a.1=b.1 := (active_canonical p a ha).symm.trans
    ((congrArg SummaryCode.encode he).trans (active_canonical p b hb))
  have haw := active_lookup p a ha
  have hbw := active_lookup p b hb
  rw [he] at haw
  exact Prod.ext hk (haw.symm.trans hbw)

theorem summaries_complete {fs : List (List Local)} (p : Plan fs) (us : List Local) (hu : us∈tuples fs) :
    CompactSummary.compactSummary us∈summaries p := by
  let k := SummaryCode.encode (CompactSummary.compactSummary us)
  have hp : 0<WeightedDP.lookup (reference fs) k := by
    rw [WeightedDP.lookup,reference_expansion]
    apply List.sum_pos_iff_exists_pos_nat.mpr
    exact ⟨1,List.mem_map.mpr ⟨us,hu,by simp [k]⟩,by decide⟩
  unfold WeightedDP.lookup WeightedDP.integral at hp
  obtain ⟨v,hv,hvp⟩ := List.sum_pos_iff_exists_pos_nat.mp hp
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hv
  have hk : e.1=k := by by_contra hn; simp [hn] at hvp
  have hn : 0<e.2 := by simpa only [hk,ite_true,Nat.mul_one] using hvp
  have ha : e∈active p := List.mem_filter.mpr ⟨by simpa only [rows_correct] using he,by simpa using hn⟩
  apply List.mem_map.mpr
  refine ⟨e,ha,?_⟩
  rw [hk,SummaryCode.decode_encode]

theorem active_integral {fs : List (List Local)} (p : Plan fs) (f : List Nat → Nat) :
    integral (active p) f=integral (rows p) f := by
  unfold active
  induction rows p with
  | nil => rfl
  | cons e rs ih =>
    by_cases h : 0<e.2
    · simp [h,ih]
    · have hz : e.2=0 := by omega
      simp [hz,ih]

end ChuShogi.SuffixSupport
