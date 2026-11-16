import ChuShogi.Placement
import ChuShogi.Indexing

/-! Construct class-preserving permutations from finite block cardinalities.
This discharges the geometric existence premise of Placement's transport lemmas. -/
namespace ChuShogi.FiniteRelabelling

variable {S K : Type} [DecidableEq S] [DecidableEq K]

structure Iso (A B : Type) where
  forward : A → B
  backward : B → A
  left_inverse : ∀ a, backward (forward a) = a
  right_inverse : ∀ b, forward (backward b) = b

def block (all : List S) (key : S → K) (a : K) : List S :=
  all.filter fun s => decide (key s = a)

def index (all : List S) (hc : ∀ s, s ∈ all) (key : S → K) (a : K)
    (s : {s // key s = a}) : Fin (block all key a).length :=
  Indexing.rank _ s.val (by simp [block,hc,s.property])

def element (all : List S) (key : S → K) (a : K)
    (i : Fin (block all key a).length) : {s // key s = a} :=
  ⟨Indexing.unrank (block all key a) i,
    of_decide_eq_true (List.mem_filter.mp (List.getElem_mem i.isLt)).2⟩

theorem element_index (all : List S) (hc : ∀ s, s ∈ all) (key : S → K) (a : K)
    (s : {s // key s = a}) : element all key a (index all hc key a s) = s := by
  apply Subtype.ext
  exact Indexing.unrank_rank _ _ _

theorem index_element (all : List S) (hn : all.Nodup) (hc : ∀ s, s ∈ all)
    (key : S → K) (a : K) (i : Fin (block all key a).length) :
    index all hc key a (element all key a i) = i := by
  exact Indexing.rank_unrank _ (hn.filter _) i

/-- Finite block bijection, constructed by list indices with matching lengths. -/
def blockIso (all : List S) (hn : all.Nodup) (hc : ∀ s, s ∈ all)
    (key₁ key₂ : S → K) (a : K) (h : (block all key₁ a).length = (block all key₂ a).length) :
    Iso {s // key₁ s = a} {s // key₂ s = a} where
  forward s := element all key₂ a (Fin.cast h (index all hc key₁ a s))
  backward t := element all key₁ a (Fin.cast h.symm (index all hc key₂ a t))
  left_inverse s := by
    rw [index_element all hn hc]
    simp only [Fin.cast_cast,Fin.cast_refl,id,element_index]
  right_inverse t := by
    rw [index_element all hn hc]
    simp only [Fin.cast_cast,Fin.cast_refl,id,element_index]

def forward (key₁ key₂ : S → K)
    (e : ∀ a, Iso {s // key₁ s = a} {s // key₂ s = a}) (s : S) : S :=
  ((e (key₁ s)).forward ⟨s,rfl⟩).val

def backward (key₁ key₂ : S → K)
    (e : ∀ a, Iso {s // key₁ s = a} {s // key₂ s = a}) (s : S) : S :=
  ((e (key₂ s)).backward ⟨s,rfl⟩).val

omit [DecidableEq S] [DecidableEq K] in
theorem forward_key (key₁ key₂ : S → K)
    (e : ∀ a, Iso {s // key₁ s = a} {s // key₂ s = a}) (s : S) :
    key₂ (forward key₁ key₂ e s) = key₁ s := ((e (key₁ s)).forward ⟨s,rfl⟩).property

omit [DecidableEq S] [DecidableEq K] in
theorem backward_at (key₁ key₂ : S → K)
    (e : ∀ a, Iso {s // key₁ s = a} {s // key₂ s = a}) (s : S) (a : K) (h : key₂ s = a) :
    backward key₁ key₂ e s = ((e a).backward ⟨s,h⟩).val := by
  cases h
  rfl

omit [DecidableEq S] [DecidableEq K] in
theorem forward_at (key₁ key₂ : S → K)
    (e : ∀ a, Iso {s // key₁ s = a} {s // key₂ s = a}) (s : S) (a : K) (h : key₁ s = a) :
    forward key₁ key₂ e s = ((e a).forward ⟨s,h⟩).val := by
  cases h
  rfl

def assemble (key₁ key₂ : S → K)
    (e : ∀ a, Iso {s // key₁ s = a} {s // key₂ s = a}) : Placement.Relabelling key₁ key₂ where
  forward := forward key₁ key₂ e
  backward := backward key₁ key₂ e
  preserves_class := forward_key key₁ key₂ e
  left_inverse s := by
    rw [backward_at key₁ key₂ e _ _ (forward_key key₁ key₂ e s)]
    exact congrArg Subtype.val ((e (key₁ s)).left_inverse ⟨s,rfl⟩)
  right_inverse s := by
    have hk : key₁ (backward key₁ key₂ e s) = key₂ s := ((e (key₂ s)).backward ⟨s,rfl⟩).property
    rw [forward_at key₁ key₂ e _ _ hk]
    exact congrArg Subtype.val ((e (key₂ s)).right_inverse ⟨s,rfl⟩)

/-- Equal sizes of all class fibres suffice; no permutation is assumed. -/
def of_counts (all : List S) (hn : all.Nodup) (hc : ∀ s, s ∈ all)
    (key₁ key₂ : S → K)
    (h : ∀ a, (block all key₁ a).length = (block all key₂ a).length) :
    Placement.Relabelling key₁ key₂ :=
  assemble key₁ key₂ (fun a => blockIso all hn hc key₁ key₂ a (h a))

/- A permutation of a complete finite square list preserves that list up to order. -/
omit [DecidableEq S] [DecidableEq K] in
theorem forward_perm (all : List S) (hn : all.Nodup) (hc : ∀ s, s ∈ all)
    {key₁ key₂ : S → K} (e : Placement.Relabelling key₁ key₂) :
    (all.map e.forward).Perm all := by
  apply (List.perm_ext_iff_of_nodup _ hn).mpr
  · intro s
    constructor
    · intro _; exact hc s
    · intro _
      exact List.mem_map.mpr ⟨e.backward s,hc _,e.right_inverse s⟩
  · rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
    apply List.Pairwise.imp _ hn
    intro a b hab he
    have hr := congrArg e.backward he
    rw [e.left_inverse,e.left_inverse] at hr
    exact hab hr

end ChuShogi.FiniteRelabelling
