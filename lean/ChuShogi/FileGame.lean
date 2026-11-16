import ChuShogi.FiniteSearch
import ChuShogi.Promotion

/-! Reference abstract file-game transitions for arbitrary slot lists.
Codes 0 and 13 mean captured and promoted. The specification uses ordered
present ranks and strengthened eligibility, independently of graph traversal. -/
namespace ChuShogi.FileGame
open Promotion

abbrev State := List (Fin 14)
abbrev Slot := Colour × Kind

def shown (r : Fin 14) : Nat := if r.val ≤ 12 then r.val else 0

def present (r : Fin 14) : Bool := 0 < r.val && r.val ≤ 12

def zone (c : Colour) (r : Nat) : Bool :=
  match c with
  | .black => 9 ≤ r
  | .white => r ≤ 4

def direction (c : Colour) (k : Kind) (r t : Nat) : Bool :=
  match k, c with
  | .pawn, .black => t = r + 1
  | .pawn, .white => t + 1 = r
  | .goBetween, _ => t = r + 1 || t + 1 = r
  | .lance, .black => r < t
  | .lance, .white => t < r
  | .chariot, _ => r ≠ t

def clear (st : State) (r t : Nat) : Bool :=
  st.all fun q => !present q || !((r < q.val && q.val ≤ t) || (t ≤ q.val && q.val < r))

def destinations (st : State) (slot : Slot) (r : Fin 14) : List (Fin 14) :=
  ((List.finRange 12).map fun t => (⟨t.val + 1, by omega⟩ : Fin 14)).filter fun t =>
    direction slot.1 slot.2 r.val t.val && clear st r.val t.val

def next (slots : List Slot) (st : State) : List State :=
  (slots.zip st).zipIdx.flatMap fun ((slot,r),i) =>
    if present r then
      [st.set i ⟨0, by omega⟩] ++
        (destinations st slot r).flatMap fun t =>
          [st.set i t] ++ if zone slot.1 r.val || zone slot.1 t.val then
            [st.set i ⟨13, by omega⟩] else []
    else []

def uFile (slots : List Slot) (st : State) : UFile := fun c k =>
  (((slots.zip st).filter fun (slot,_) => decide (slot = (c,k))).map fun (_,r) => shown r).sum

def orderedSlot (slot : Slot) : OrderedFile.Slot :=
  match slot with
  | (.black, .pawn) => .blackPawn
  | (.white, .pawn) => .whitePawn
  | _ => .other

def Classified (slots : List Slot) (st : State) : Prop :=
  st.length = slots.length ∧
  OrderedFile.Admissible (slots.map orderedSlot) (st.map shown) ∧
  ((slots.zip st).all fun (slot,r) =>
    decide (r.val ≠ 13 ∨ Eligible (uFile slots st) slot.1 slot.2)) = true ∧
  ((slots.zip st).filter fun (slot,r) => decide (slot.2 = .pawn ∧ r.val = 13)).length ≤ 1

/-- A computable version of the independent ordered-rank specification. -/
instance orderedDecidable (u : List Nat) : Decidable (OrderedFile.Ordered u) :=
  match u with
  | [] => isTrue trivial
  | r :: rs =>
    let _ := orderedDecidable rs
    inferInstanceAs (Decidable ((∀ t ∈ rs, r = 0 ∨ t = 0 ∨ r < t) ∧ OrderedFile.Ordered rs))

instance boundedDecidable (slots : List OrderedFile.Slot) (u : List Nat) :
    Decidable (OrderedFile.Bounded slots u) :=
  match slots, u with
  | [], rs => inferInstanceAs (Decidable (rs = []))
  | _ :: _, [] => isFalse (by rintro ⟨r, tail, h, _⟩; cases h)
  | s :: ss, r :: rs =>
    let _ := boundedDecidable ss rs
    decidable_of_iff ((r = 0 ∨ OrderedFile.RankAllowed s r) ∧ OrderedFile.Bounded ss rs) (by
      constructor
      · rintro ⟨hr, ht⟩; exact ⟨r,rs,rfl,hr,ht⟩
      · rintro ⟨t,tail,h,hr,ht⟩; cases h; exact ⟨hr,ht⟩)

instance classifiedDecidable (slots : List Slot) (st : State) : Decidable (Classified slots st) := by
  unfold Classified OrderedFile.Admissible
  infer_instance

/-- Balanced search tree, used only as a finite certificate representation. -/
inductive Tree where
  | empty
  | node (state : State) (left right : Tree)

/-- Fixed-length base-14 coding. Equality is checked separately during lookup. -/
def code (s : State) : Nat := s.foldl (fun n r => 14 * n + r.val) 0

def contains (s : State) : Tree → Bool
  | .empty => false
  | .node t l r => if s = t then true else if code s < code t then contains s l else contains s r

def All (p : State → Prop) : Tree → Prop
  | .empty => True
  | .node s l r => p s ∧ All p l ∧ All p r

instance allDecidable (p : State → Prop) [DecidablePred p] (tree : Tree) : Decidable (All p tree) :=
  match tree with
  | .empty => isTrue trivial
  | .node _ l r =>
    let _ := allDecidable p l
    let _ := allDecidable p r
    inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem contains_all (p : State → Prop) (tree : Tree) (h : All p tree)
    (s : State) (hs : contains s tree = true) : p s := by
  induction tree with
  | empty => simp [contains] at hs
  | node t l r il ir =>
    simp only [contains] at hs
    split at hs
    · rename_i he; subst s; exact h.1
    · split at hs
      · exact il h.2.1 hs
      · exact ir h.2.2 hs

def listing : Tree → List State
  | .empty => []
  | .node s l r => s :: (listing l ++ listing r)

theorem listing_all (p : State → Prop) (tree : Tree) (h : All p tree) :
    ∀ s ∈ listing tree, p s := by
  induction tree with
  | empty => simp [listing]
  | node t l r il ir =>
    intro s hs
    simp only [listing, List.mem_cons, List.mem_append] at hs
    rcases hs with he | hl | hr
    · subst s; exact h.1
    · exact il h.2.1 s hl
    · exact ir h.2.2 s hr

theorem contains_mem (tree : Tree) (s : State) (hs : contains s tree = true) :
    s ∈ listing tree := by
  induction tree with
  | empty => simp [contains] at hs
  | node t l r il ir =>
    simp only [contains] at hs
    simp only [listing, List.mem_cons, List.mem_append]
    split at hs
    · exact Or.inl ‹s = t›
    · right
      split at hs
      · exact Or.inl (il hs)
      · exact Or.inr (ir hs)

/-- Interval certificate makes uniqueness linear to check rather than quadratic. -/
def BoundedTree (lo hi : Nat) : Tree → Prop
  | .empty => True
  | .node s l r => lo ≤ code s ∧ code s < hi ∧
      BoundedTree lo (code s) l ∧ BoundedTree (code s + 1) hi r

instance boundedTreeDecidable (lo hi : Nat) (tree : Tree) : Decidable (BoundedTree lo hi tree) :=
  match tree with
  | .empty => isTrue trivial
  | .node s l r =>
    let _ := boundedTreeDecidable lo (code s) l
    let _ := boundedTreeDecidable (code s + 1) hi r
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem bounded_codes (tree : Tree) (lo hi : Nat) (h : BoundedTree lo hi tree) :
    ∀ s ∈ listing tree, lo ≤ code s ∧ code s < hi := by
  induction tree generalizing lo hi with
  | empty => simp [listing]
  | node t l r il ir =>
    intro s hs
    simp only [listing, List.mem_cons, List.mem_append] at hs
    rcases hs with he | hl | hr
    · subst s; exact ⟨h.1,h.2.1⟩
    · have hc := il _ _ h.2.2.1 s hl
      exact ⟨hc.1, Nat.lt_trans hc.2 h.2.1⟩
    · have hc := ir _ _ h.2.2.2 s hr
      have hlo := h.1
      exact ⟨by omega,hc.2⟩

theorem bounded_nodup (tree : Tree) (lo hi : Nat) (h : BoundedTree lo hi tree) :
    (listing tree).Nodup := by
  induction tree generalizing lo hi with
  | empty => simp [listing]
  | node t l r il ir =>
    rw [listing, List.nodup_cons, List.nodup_append]
    refine ⟨?_, il _ _ h.2.2.1, ir _ _ h.2.2.2, ?_⟩
    · intro ht
      rcases List.mem_append.mp ht with hl | hr
      · have hc := bounded_codes l _ _ h.2.2.1 t hl; omega
      · have hc := bounded_codes r _ _ h.2.2.2 t hr; omega
    · intro a ha b hb he
      have hl := bounded_codes l _ _ h.2.2.1 a ha
      have hr := bounded_codes r _ _ h.2.2.2 b hb
      subst b
      omega

/-- Certificate closure suffices for completeness of all finite or infinite paths. -/
theorem reach_contained (slots : List Slot) (initial : State) (tree : Tree)
    (hi : contains initial tree = true)
    (hc : All (fun s => (next slots s).all (fun t => contains t tree) = true) tree)
    (s : State) (hs : FiniteSearch.Reach (next slots) initial s) : contains s tree = true := by
  induction hs with
  | initial => exact hi
  | @step s t _ ht ih =>
    exact (List.all_eq_true.mp (contains_all _ tree hc s ih)) t ht

def goBetweenSlots : List Slot :=
  [(.black,.pawn), (.black,.goBetween), (.white,.goBetween), (.white,.pawn)]

def goBetweenInitial : State := [⟨4,by omega⟩,⟨5,by omega⟩,⟨8,by omega⟩,⟨9,by omega⟩]

end ChuShogi.FileGame
