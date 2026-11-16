import ChuShogi.SummarySufficiency

/-! Converse bridge: every independently admissible concrete DP tuple renders
as exactly one confined I1--I3 Board. No table completeness premise is assumed. -/
namespace ChuShogi.TupleRendering
open Specification Promotion ConcreteDP BoardDecomposition SummaryBridge Rendering

def lookup (ls : List Label) (rs : List Nat) (l : Label) : Nat :=
  (((ls.zip rs).filter fun p => decide (p.1 = l)).map Prod.snd).sum

theorem lookup_absent (ls : List Label) (rs : List Nat) (l : Label) (h : l ∉ ls) : lookup ls rs l = 0 := by
  unfold lookup
  have he : ((ls.zip rs).filter fun p => decide (p.1 = l)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    have hn : p.1 ≠ l := by
      intro he
      exact h (he ▸ (List.of_mem_zip hp).1)
    simp [hn]
  simp [he]

theorem lookup_row (ls : List Label) (hn : ls.Nodup) (rs : List Nat) (l : Label) (r : Nat)
    (hm : (l,r) ∈ ls.zip rs) : lookup ls rs l = r := by
  induction ls generalizing rs with
  | nil => simp at hm
  | cons a ls ih =>
    cases rs with
    | nil => simp at hm
    | cons t rs =>
      have hh := List.nodup_cons.mp hn
      simp only [List.zip_cons_cons,List.mem_cons] at hm
      rcases hm with he | ht
      · cases he
        unfold lookup
        simp only [List.zip_cons_cons,List.filter_cons]
        simp only [decide_true,ite_true,List.map_cons,List.sum_cons]
        rw [show (((ls.zip rs).filter fun p => decide (p.1 = l)).map Prod.snd).sum = 0 from lookup_absent ls rs l hh.1]
        omega
      · have hl := (List.of_mem_zip ht).1
        have hne : a ≠ l := fun he => hh.1 (he ▸ hl)
        unfold lookup
        simp only [List.zip_cons_cons,List.filter_cons]
        simp only [hne,decide_false,Bool.false_eq_true,ite_false]
        exact ih hh.2 rs ht

theorem lookup_present (ls : List Label) (hn : ls.Nodup) (rs : List Nat) (l : Label)
    (h : lookup ls rs l ≠ 0) : ∃ r, (l,r) ∈ ls.zip rs ∧ lookup ls rs l = r := by
  have he : ((ls.zip rs).filter fun p => decide (p.1 = l)) ≠ [] := by
    intro he
    apply h
    simp [lookup,he]
  cases hh : ((ls.zip rs).filter fun p => decide (p.1 = l)) with
  | nil => exact False.elim (he hh)
  | cons p ps =>
    have hm : p ∈ ((ls.zip rs).filter fun p => decide (p.1 = l)) := by rw [hh]; simp
    have hp := List.mem_filter.mp hm
    have hl : p.1 = l := of_decide_eq_true hp.2
    refine ⟨p.2,?_,?_⟩
    · simpa only [← hl] using hp.1
    · exact lookup_row ls hn rs l p.2 (by simpa only [← hl] using hp.1)

theorem bounded_length (ls : List OrderedFile.Slot) (rs : List Nat) (h : OrderedFile.Bounded ls rs) :
    ls.length = rs.length := by
  induction ls generalizing rs with
  | nil => subst rs; rfl
  | cons l ls ih =>
    obtain ⟨r,tail,rfl,_,ht⟩ := h
    simp only [List.length_cons,ih tail ht]

theorem bounded_row (ls : List Label) (rs : List Nat)
    (h : OrderedFile.Bounded (ls.map orderedLabel) rs) (l : Label) (r : Nat) (hm : (l,r) ∈ ls.zip rs) :
    r = 0 ∨ OrderedFile.RankAllowed (orderedLabel l) r := by
  induction ls generalizing rs with
  | nil => simp at hm
  | cons a ls ih =>
    obtain ⟨t,tail,rfl,hb,ht⟩ := h
    simp only [List.zip_cons_cons,List.mem_cons] at hm
    rcases hm with he | he
    · cases he; exact hb
    · exact ih tail ht he

def RowOrder (p q : Label × Nat) : Prop :=
  confinedStart p.1.1 p.1.2 < confinedStart q.1.1 q.1.2 ∧
    (p.2 = 0 ∨ q.2 = 0 ∨ p.2 < q.2)

theorem rows_ordered (ls : List Label) (rs : List Nat)
    (hl : ls.Pairwise (fun l m => confinedStart l.1 l.2 < confinedStart m.1 m.2))
    (hr : OrderedFile.Ordered rs) : (ls.zip rs).Pairwise RowOrder := by
  induction ls generalizing rs with
  | nil => simp
  | cons l ls ih =>
    cases rs with
    | nil => simp
    | cons r rs =>
      rw [List.zip_cons_cons,List.pairwise_cons]
      have hh := List.pairwise_cons.mp hl
      refine ⟨?_,ih rs hh.2 hr.2⟩
      intro p hp
      have hm := List.of_mem_zip hp
      exact ⟨hh.1 p.1 hm.1,hr.1 p.2 hm.2⟩

theorem pairwise_members {A : Type} (ls : List A) (R : A → A → Prop) (h : ls.Pairwise R)
    (a b : A) (ha : a ∈ ls) (hb : b ∈ ls) : a = b ∨ R a b ∨ R b a := by
  induction ls with
  | nil => simp at ha
  | cons x xs ih =>
    have hh := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with he | ha
    · subst a
      rcases List.mem_cons.mp hb with he | hb
      · exact Or.inl he.symm
      · exact Or.inr (Or.inl (hh.1 b hb))
    · rcases List.mem_cons.mp hb with he | hb
      · subst b; exact Or.inr (Or.inr (hh.1 a ha))
      · exact ih hh.2 ha hb

/-- The declarative local enumeration supplies all SlotValid clauses. -/
theorem local_properties (v : Local) (h : LocalAdmissible v.1 v) :
    (∀ c k, ¬ HasSlot v.1 c k → localU v c k = 0) ∧
    (∀ c k, localU v c k = 0 ∨ OrderedFile.RankAllowed (orderedLabel (c,k)) (localU v c k)) ∧
    (∀ c d k l, confinedStart c k < confinedStart d l →
      localU v c k ≠ 0 → localU v d l ≠ 0 → localU v c k < localU v d l) := by
  have hv : OrderedFile.Admissible ((labels v.1).map orderedLabel) v.2 := h.2
  have hn := labels_nodup v.1
  change (∀ c k, ¬ HasSlot v.1 c k → lookup (labels v.1) v.2 (c,k) = 0) ∧ _
  refine ⟨?_,?_,?_⟩
  · intro c k hs
    exact lookup_absent _ _ _ (fun hm => hs ((labels_membership v.1 c k).mp hm))
  · intro c k
    by_cases hz : localU v c k = 0
    · exact Or.inl hz
    · obtain ⟨r,hr,he⟩ := lookup_present _ hn v.2 (c,k) hz
      have he' : localU v c k = r := he
      rw [he']
      exact bounded_row _ _ hv.1 (c,k) r hr
  · intro c d k l ho hnz hmz
    obtain ⟨r,hr,he⟩ := lookup_present _ hn v.2 (c,k) hnz
    obtain ⟨t,ht,hf⟩ := lookup_present _ hn v.2 (d,l) hmz
    have he' : localU v c k = r := he
    have hf' : localU v d l = t := hf
    have hp := rows_ordered _ _ (labels_ordered v.1) hv.2
    rcases pairwise_members _ RowOrder hp ((c,k),r) ((d,l),t) hr ht with hh | hh | hh
    · have hlabel := congrArg (fun p : Label × Nat => confinedStart p.1.1 p.1.2) hh
      change confinedStart c k = confinedStart d l at hlabel
      omega
    · have hrr : r ≠ 0 := by simpa only [he'] using hnz
      have htt : t ≠ 0 := by simpa only [hf'] using hmz
      have hlt := (hh.2.resolve_left hrr).resolve_left htt
      change lookup (labels v.1) v.2 (c,k) < lookup (labels v.1) v.2 (d,l)
      rwa [he,hf]
    · have hh' := hh.1
      change confinedStart d l < confinedStart c k at hh'
      omega

/-- Lookup reconstructs an entire row list when the labels occur exactly once. -/
theorem lookup_reconstruct (ls : List Label) (rs : List Nat) (hn : ls.Nodup) (hl : ls.length = rs.length) :
    ls.map (lookup ls rs) = rs := by
  apply List.ext_getElem
  · simpa using hl
  · intro i hi hj
    have hil : i < ls.length := by simpa using hi
    rw [List.getElem_map]
    apply lookup_row ls hn rs _ _
    exact (by
      have hzi : i < (ls.zip rs).length := by simp [List.length_zip]; omega
      have hm := List.getElem_mem (l := ls.zip rs) hzi
      simpa using hm)

theorem valid_shape (xs : List (Fin 12)) (us : List Local)
    (h : WeightedDP.Valid (xs.map LocalAdmissible) us) :
    us.map Prod.fst = xs ∧ ∀ v ∈ us, LocalAdmissible v.1 v := by
  induction xs generalizing us with
  | nil => subst us; exact ⟨rfl,by simp⟩
  | cons x xs ih =>
    obtain ⟨v,tail,rfl,hv,ht⟩ := h
    have hh := ih tail ht
    refine ⟨?_,?_⟩
    · simp only [List.map_cons,hh.1,hv.1]
    · intro w hw
      rcases List.mem_cons.mp hw with he | he
      · subst w
        exact ⟨rfl,by rw [hv.1]; exact hv.2⟩
      · exact hh.2 w he

theorem entry_exists (us : List Local) (h : ConcreteDP.Valid us) (x : Fin 12) :
    ∃ v, v ∈ us ∧ v.1 = x := by
  have hs := (valid_shape indices us h).1
  have hm : x ∈ us.map Prod.fst := by rw [hs]; simp [indices]
  exact List.mem_map.mp hm

theorem entry_unique (us : List Local) (h : ConcreteDP.Valid us) (v w : Local)
    (hv : v ∈ us) (hw : w ∈ us) (he : v.1 = w.1) : v = w := by
  have hs := (valid_shape indices us h).1
  have hn : (us.map Prod.fst).Nodup := by rw [hs]; decide
  change (us.map Prod.fst).Pairwise (fun a b => a ≠ b) at hn
  rw [List.pairwise_map] at hn
  rcases pairwise_members us _ hn v w hv hw with hh | hh | hh
  · exact hh
  · exact False.elim (hh he)
  · exact False.elim (hh he.symm)

noncomputable def entry (us : List Local) (h : ConcreteDP.Valid us) (x : Fin 12) : Local :=
  Classical.choose (entry_exists us h x)

theorem entry_spec (us : List Local) (h : ConcreteDP.Valid us) (x : Fin 12) :
    entry us h x ∈ us ∧ (entry us h x).1 = x := Classical.choose_spec (entry_exists us h x)

noncomputable def decode (us : List Local) (h : ConcreteDP.Valid us) : Slots :=
  fun x => localU (entry us h x)

theorem decode_valid (us : List Local) (h : ConcreteDP.Valid us) : SlotValid (decode us h) := by
  have hp (x : Fin 12) := local_properties (entry us h x)
    ((valid_shape indices us h).2 _ (entry_spec us h x).1)
  have hn (x : Fin 12) :
      (∀ c k, ¬ HasSlot x c k → decode us h x c k = 0) ∧
      (∀ c k, decode us h x c k = 0 ∨ OrderedFile.RankAllowed (orderedLabel (c,k)) (decode us h x c k)) ∧
      (∀ c d k l, confinedStart c k < confinedStart d l →
        decode us h x c k ≠ 0 → decode us h x d l ≠ 0 → decode us h x c k < decode us h x d l) := by
    have hh := hp x
    rw [(entry_spec us h x).2] at hh
    exact hh
  exact ⟨fun x => (hn x).1,fun x => (hn x).2.1,fun x => (hn x).2.2⟩

theorem decode_entry (us : List Local) (h : ConcreteDP.Valid us) (v : Local) (hv : v ∈ us) :
    decode us h v.1 = localU v := by
  unfold decode
  rw [entry_unique us h _ v (entry_spec us h v.1).1 hv (entry_spec us h v.1).2]

noncomputable def renderTuple (us : List Local) (h : ConcreteDP.Valid us) : Board := render (decode us h)

theorem renderTuple_local (us : List Local) (h : ConcreteDP.Valid us) (v : Local) (hv : v ∈ us) :
    boardLocal (renderTuple us h) v.1 = v := by
  have hh := (valid_shape indices us h).2 v hv
  have hl : (labels v.1).length = v.2.length := by
    have he := bounded_length _ _ hh.2.1
    simpa using he
  apply Prod.ext
  · rfl
  change (labels v.1).map (fun l => unpromoted (render (decode us h)) v.1 l.1 l.2) = v.2
  rw [unpromoted_render _ (decode_valid us h),decode_entry us h v hv]
  exact lookup_reconstruct _ _ (labels_nodup v.1) hl

theorem boardTuple_renderTuple (us : List Local) (h : ConcreteDP.Valid us) :
    boardTuple (renderTuple us h) = us := by
  unfold boardTuple
  rw [← (valid_shape indices us h).1,List.map_map]
  have he : us.map (fun v => boardLocal (renderTuple us h) v.1) = us.map id := by
    apply List.map_congr_left
    intro v hv
    exact renderTuple_local us h v hv
  exact he.trans (by simp)

/-- No application-specific validity assumption on the enumeration remains. -/
noncomputable def tupleBoardIso :
    FiniteRelabelling.Iso {us : List Local // ConcreteDP.Valid us}
      {b : Board // OnlyConfined b ∧ I1 b ∧ I2 b ∧ I3 b} where
  forward us := ⟨renderTuple us.val us.property,render_onlyConfined _,
    render_I1 _ (decode_valid us.val us.property),render_I2 _ (decode_valid us.val us.property),
    render_I3 _ (decode_valid us.val us.property)⟩
  backward b := ⟨boardTuple b.val,boardTuple_valid b.val b.property.2.1 b.property.2.2.1 b.property.2.2.2⟩
  left_inverse us := by
    apply Subtype.ext
    exact boardTuple_renderTuple us.val us.property
  right_inverse b := by
    apply Subtype.ext
    apply boardTuple_injective _ b.val
      (render_I1 _ (decode_valid _ _)) b.property.2.1
      (render_onlyConfined _) b.property.1
    exact boardTuple_renderTuple _ _

end ChuShogi.TupleRendering

