import ChuShogi.GeneralFileCoordinates
import ChuShogi.FileTupleCodec

/-! Computed inverse from a valid tuple and terminal index to recursive file
coordinates. Local rank uses the original complete lists; no tuple-product
or Board-product enumeration is executed. -/
namespace ChuShogi.GeneralTupleCodec
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
open ConcreteDP GeneralFileCoordinates FileBranchCoordinates
open FileTupleCodec (cons_mem nil_not_mem)

def encode (finish : Summary → Nat) : (fs : List (List Local)) → (p : Summary) → (us : List Local) →
    (hm : us ∈ WeightedDP.tuples fs) → Fin (finish (add p (CompactSummary.compactSummary us))) → Code finish fs p
  | [],p,us,hm,k => by
    have he : us=[] := by simpa [WeightedDP.tuples] using hm
    exact ⟨k.val,by simpa [he,CompactSummary.compactSummary,WeightedDP.summary,add_zero] using k.isLt⟩
  | xs::fs,_,[],hm,_ => False.elim (nil_not_mem xs fs hm)
  | xs::fs,p,u::us,hm,k =>
    let hu := (cons_mem xs fs u us).mp hm
    let i := Indexing.rank xs u hu.1
    have hi : xs[i.val]=u := Indexing.unrank_rank xs u hu.1
    ⟨i,encode finish fs (add p (CompactSummary.compactFeature xs[i.val])) us hu.2
      ⟨k.val,by simpa only [CompactSummary.compactSummary,WeightedDP.summary,hi,← add_swap]
        using k.isLt⟩⟩

theorem tuple_encode (finish : Summary → Nat) (fs : List (List Local)) (p : Summary) (us : List Local)
    (hm : us ∈ WeightedDP.tuples fs) (k : Fin (finish (add p (CompactSummary.compactSummary us)))) :
    tuple finish fs p (encode finish fs p us hm k)=us := by
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

theorem leaf_encode (finish : Summary → Nat) (fs : List (List Local)) (p : Summary) (us : List Local)
    (hm : us ∈ WeightedDP.tuples fs) (k : Fin (finish (add p (CompactSummary.compactSummary us)))) :
    (leaf finish fs p (encode finish fs p us hm k)).val=k.val := by
  induction fs generalizing p us with
  | nil => rfl
  | cons xs fs ih =>
    cases us with
    | nil => exact False.elim (nil_not_mem xs fs hm)
    | cons u us => exact ih _ us _ _

abbrev Coordinates (finish : Summary → Nat) (fs : List (List Local)) (p : Summary) :=
  Σ us : {us : List Local // us ∈ WeightedDP.tuples fs}, Fin (finish (add p (CompactSummary.compactSummary us.val)))

@[irreducible] def forward (finish : Summary → Nat) (fs : List (List Local)) (p : Summary) (x : Code finish fs p) : Coordinates finish fs p :=
  ⟨⟨tuple finish fs p x,tuple_mem finish fs p x⟩,
    ⟨(leaf finish fs p x).val,by rw [← final_summary finish fs p x]; exact (leaf finish fs p x).isLt⟩⟩

theorem forward_tuple (finish : Summary → Nat) (fs : List (List Local)) (p : Summary) (x : Code finish fs p) :
    (forward finish fs p x).1.val=tuple finish fs p x := by unfold forward; rfl
theorem forward_leaf (finish : Summary → Nat) (fs : List (List Local)) (p : Summary) (x : Code finish fs p) :
    (forward finish fs p x).2.val=(leaf finish fs p x).val := by unfold forward; rfl

def backward (finish : Summary → Nat) (fs : List (List Local)) (p : Summary) (x : Coordinates finish fs p) : Code finish fs p :=
  encode finish fs p x.1.val x.1.property x.2

theorem coordinates_ext (x y : Coordinates finish fs p) (hu : x.1.val=y.1.val) (hk : x.2.val=y.2.val) : x=y := by
  rcases x with ⟨⟨us,hm⟩,i⟩
  rcases y with ⟨⟨vs,hn⟩,j⟩
  change us=vs at hu
  subst vs
  have hi : i=j := Fin.ext hk
  subst j
  rfl

@[irreducible] def equivalence (finish : Summary → Nat) (fs : List (List Local)) (hn : ∀ xs∈fs, xs.Nodup) (p : Summary) :
    Code finish fs p ≃ Coordinates finish fs p where
  toFun := forward finish fs p
  invFun := backward finish fs p
  left_inv x := by
    apply GeneralFileCoordinates.coordinates_injective finish fs hn p
    · change tuple finish fs p (encode finish fs p _ _ _) = _
      rw [tuple_encode,forward_tuple]
    · change (leaf finish fs p (encode finish fs p _ _ _)).val = _
      rw [leaf_encode,forward_leaf]
  right_inv x := by
    apply coordinates_ext
    · rw [forward_tuple]
      exact tuple_encode finish fs p _ _ _
    · rw [forward_leaf]
      exact leaf_encode finish fs p _ _ _

end ChuShogi.GeneralTupleCodec
