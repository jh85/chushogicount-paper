import ChuShogi.FileBranchSemantics

/-! Computed inverse from a valid tuple and terminal index to recursive file
coordinates. Local rank uses the original complete lists; no tuple-product
or Board-product enumeration is executed. -/
namespace ChuShogi.FileTupleCodec
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
open ConcreteDP FileBranchCoordinates FileBranchSemantics

theorem cons_mem (xs : List Local) (fs : List (List Local)) (u : Local) (us : List Local) :
    u::us ∈ WeightedDP.tuples (xs::fs) ↔ u∈xs ∧ us∈WeightedDP.tuples fs := by
  simp only [WeightedDP.tuples,List.mem_flatMap,List.mem_map]
  constructor
  · rintro ⟨v,hv,vs,ht,he⟩
    cases he
    exact ⟨hv,ht⟩
  · rintro ⟨hu,ht⟩; exact ⟨u,hu,us,ht,rfl⟩

theorem nil_not_mem (xs : List Local) (fs : List (List Local)) : [] ∉ WeightedDP.tuples (xs::fs) := by
  simp [WeightedDP.tuples]

def encode (r : Bool) : (fs : List (List Local)) → (p : Summary) → (us : List Local) →
    (hm : us ∈ WeightedDP.tuples fs) → Fin (terminal r (add p (CompactSummary.compactSummary us))) → Code r fs p
  | [],p,us,hm,k => by
    have he : us=[] := by simpa [WeightedDP.tuples] using hm
    exact ⟨k.val,by simpa [he,CompactSummary.compactSummary,WeightedDP.summary,add_zero] using k.isLt⟩
  | xs::fs,_,[],hm,_ => False.elim (nil_not_mem xs fs hm)
  | xs::fs,p,u::us,hm,k =>
    let hu := (cons_mem xs fs u us).mp hm
    let i := Indexing.rank xs u hu.1
    have hi : xs[i.val]=u := Indexing.unrank_rank xs u hu.1
    ⟨i,encode r fs (add p (CompactSummary.compactFeature xs[i.val])) us hu.2
      ⟨k.val,by simpa only [CompactSummary.compactSummary,WeightedDP.summary,hi,← add_swap]
        using k.isLt⟩⟩

theorem tuple_encode (r : Bool) (fs : List (List Local)) (p : Summary) (us : List Local)
    (hm : us ∈ WeightedDP.tuples fs) (k : Fin (terminal r (add p (CompactSummary.compactSummary us)))) :
    tuple r fs p (encode r fs p us hm k)=us := by
  induction fs generalizing p us with
  | nil =>
    have he : us=[] := by simpa [WeightedDP.tuples] using hm
    exact he.symm
  | cons xs fs ih =>
    cases us with
    | nil => exact False.elim (nil_not_mem xs fs hm)
    | cons u us =>
      change xs[(Indexing.rank xs u ((cons_mem xs fs u us).mp hm).1).val]::_=u::us
      rw [show xs[(Indexing.rank xs u ((cons_mem xs fs u us).mp hm).1).val]=u from
        Indexing.unrank_rank xs u _]
      congr 1
      exact ih _ us _ _

theorem leaf_encode (r : Bool) (fs : List (List Local)) (p : Summary) (us : List Local)
    (hm : us ∈ WeightedDP.tuples fs) (k : Fin (terminal r (add p (CompactSummary.compactSummary us)))) :
    (leafIndex r fs p (encode r fs p us hm k)).val=k.val := by
  induction fs generalizing p us with
  | nil => rfl
  | cons xs fs ih =>
    cases us with
    | nil => exact False.elim (nil_not_mem xs fs hm)
    | cons u us => exact ih _ us _ _

abbrev Coordinates (r : Bool) (fs : List (List Local)) (p : Summary) :=
  Σ us : {us : List Local // us ∈ WeightedDP.tuples fs}, Fin (terminal r (add p (CompactSummary.compactSummary us.val)))

@[irreducible] def forward (r : Bool) (fs : List (List Local)) (p : Summary) (x : Code r fs p) : Coordinates r fs p :=
  ⟨⟨tuple r fs p x,tuple_mem r fs p x⟩,
    ⟨(leafIndex r fs p x).val,by rw [← final_summary r fs p x]; exact (leafIndex r fs p x).isLt⟩⟩

theorem forward_tuple (r : Bool) (fs : List (List Local)) (p : Summary) (x : Code r fs p) :
    (forward r fs p x).1.val=tuple r fs p x := by unfold forward; rfl
theorem forward_leaf (r : Bool) (fs : List (List Local)) (p : Summary) (x : Code r fs p) :
    (forward r fs p x).2.val=(leafIndex r fs p x).val := by unfold forward; rfl

def backward (r : Bool) (fs : List (List Local)) (p : Summary) (x : Coordinates r fs p) : Code r fs p :=
  encode r fs p x.1.val x.1.property x.2

theorem coordinates_ext (x y : Coordinates r fs p) (hu : x.1.val=y.1.val) (hk : x.2.val=y.2.val) : x=y := by
  rcases x with ⟨⟨us,hm⟩,i⟩
  rcases y with ⟨⟨vs,hn⟩,j⟩
  change us=vs at hu
  subst vs
  have hi : i=j := Fin.ext hk
  subst j
  rfl

@[irreducible] def equivalence (r : Bool) (fs : List (List Local)) (hn : ∀ xs∈fs, xs.Nodup) (p : Summary) :
    Code r fs p ≃ Coordinates r fs p where
  toFun := forward r fs p
  invFun := backward r fs p
  left_inv x := by
    apply coordinates_injective r fs hn p
    · change tuple r fs p (encode r fs p _ _ _) = _
      rw [tuple_encode,forward_tuple]
    · change (leafIndex r fs p (encode r fs p _ _ _)).val = _
      rw [leaf_encode,forward_leaf]
  right_inv x := by
    apply coordinates_ext
    · rw [forward_tuple]
      exact tuple_encode r fs p _ _ _
    · rw [forward_leaf]
      exact leaf_encode r fs p _ _ _

end ChuShogi.FileTupleCodec
