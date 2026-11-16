import ChuShogi.WeightedDP
import ChuShogi.Indexing

/-!
Independent present-piece specifications for all three confined-file types.
Ranks are 0 (absent) or displayed ranks 1--12. Slot identities are fixed by
position in the slot list, so absent pieces have no capture/promotion label.
-/
namespace ChuShogi.OrderedFile

inductive Slot where
  | blackPawn | whitePawn | other
  deriving DecidableEq, Repr

/-- Bounds on a present slot, independently of enumeration. -/
def RankAllowed (s : Slot) (r : Nat) : Prop :=
  1 ≤ r ∧ r ≤ 12 ∧ (s = .blackPawn → 4 ≤ r) ∧ (s = .whitePawn → r ≤ 9)

instance (s : Slot) (r : Nat) : Decidable (RankAllowed s r) :=
  inferInstanceAs (Decidable (1 ≤ r ∧ r ≤ 12 ∧
    (s = .blackPawn → 4 ≤ r) ∧ (s = .whitePawn → r ≤ 9)))

/-- I2: every surviving slot is strictly below every later surviving slot. -/
def Ordered : List Nat → Prop
  | [] => True
  | r :: rs => (∀ t ∈ rs, r = 0 ∨ t = 0 ∨ r < t) ∧ Ordered rs

/-- I3 and the board's rank bounds, with I1 implicit in fixed slot identities. -/
def Bounded : List Slot → List Nat → Prop
  | [], rs => rs = []
  | s :: ss, rs => ∃ r tail, rs = r :: tail ∧
      (r = 0 ∨ RankAllowed s r) ∧ Bounded ss tail

def Admissible (slots : List Slot) (u : List Nat) : Prop :=
  Bounded slots u ∧ Ordered u

/-- Auxiliary lower bound is a mathematical condition on all present ranks. -/
def Above (lo : Nat) (u : List Nat) : Prop := ∀ r ∈ u, r = 0 ∨ lo < r

def choices (lo : Nat) (s : Slot) : List Nat :=
  ((List.range 12).map (· + 1)).filter fun r => decide (lo < r ∧ RankAllowed s r)

def enumerate (lo : Nat) : List Slot → List (List Nat)
  | [] => [[]]
  | s :: ss => (enumerate lo ss).map (0 :: ·) ++
      (choices lo s).flatMap fun r => (enumerate r ss).map (r :: ·)

theorem choices_iff (lo : Nat) (s : Slot) (r : Nat) :
    r ∈ choices lo s ↔ lo < r ∧ RankAllowed s r := by
  simp only [choices, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨r - 1, ?_, ?_⟩, h⟩ <;> have hr := h.2 <;> unfold RankAllowed at hr <;> omega

theorem enumerate_iff (slots : List Slot) (lo : Nat) (u : List Nat) :
    u ∈ enumerate lo slots ↔ Admissible slots u ∧ Above lo u := by
  induction slots generalizing lo u with
  | nil => cases u <;> simp [enumerate, Admissible, Bounded, Ordered, Above]
  | cons s ss ih =>
    cases u with
    | nil => simp [enumerate, Admissible, Bounded]
    | cons r rs =>
      simp only [enumerate, List.mem_append, List.mem_map, List.mem_flatMap,
        List.cons.injEq]
      simp only [Admissible, Bounded, Ordered, Above]
      constructor
      · intro h
        rcases h with ⟨tail, ht, hzero, heq⟩ | ⟨t, ht, tail, hu, heq, htail⟩
        · subst r; subst tail
          have hv := (ih lo rs).mp ht
          refine ⟨⟨⟨0, rs, rfl, Or.inl rfl, hv.1.1⟩, ?_, hv.1.2⟩, ?_⟩
          · intro t _; exact Or.inl rfl
          · intro t ht
            rcases List.mem_cons.mp ht with h | h
            · exact Or.inl h
            · exact hv.2 t h
        · subst t; subst tail
          have hc := (choices_iff lo s r).mp ht
          have hv := (ih r rs).mp hu
          refine ⟨⟨⟨r, rs, rfl, Or.inr hc.2, hv.1.1⟩, ?_, hv.1.2⟩, ?_⟩
          · intro t ht; exact Or.inr (hv.2 t ht)
          · intro t ht
            rcases List.mem_cons.mp ht with h | h
            · subst t; exact Or.inr hc.1
            · rcases hv.2 t h with hz | hr
              · exact Or.inl hz
              · exact Or.inr (Nat.lt_trans hc.1 hr)
      · rintro ⟨⟨⟨t, tail, heq, hr, hb⟩, ho, hot⟩, ha⟩
        cases heq
        by_cases hz : r = 0
        · subst r
          left
          exact ⟨rs, (ih lo rs).mpr ⟨⟨hb, hot⟩, fun t ht => ha t (by simp [ht])⟩, rfl, rfl⟩
        · right
          have hp := hr.resolve_left hz
          refine ⟨r, (choices_iff lo s r).mpr ⟨(ha r (by simp)).resolve_left hz, hp⟩,
            rs, (ih r rs).mpr ⟨⟨hb, hot⟩, ?_⟩, rfl, rfl⟩
          intro t ht
          exact (ho t ht).resolve_left hz

theorem choices_nodup (lo : Nat) (s : Slot) : (choices lo s).Nodup := by
  apply List.Pairwise.filter
  change List.Pairwise _ _
  rw [List.pairwise_map]
  apply List.Pairwise.imp _ (List.nodup_range (n := 12))
  intro a b hab heq
  exact hab (Nat.add_right_cancel heq)

theorem enumerate_nodup (slots : List Slot) (lo : Nat) : (enumerate lo slots).Nodup := by
  induction slots generalizing lo with
  | nil => simp [enumerate]
  | cons s ss ih =>
    simp only [enumerate, List.nodup_iff_pairwise_ne, List.pairwise_append,
      List.pairwise_flatMap, List.pairwise_map]
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · apply List.Pairwise.imp _ (ih lo)
      intro a b hab heq; exact hab (List.cons.inj heq).2
    · intro r _
      apply List.Pairwise.imp _ (ih r)
      intro a b hab heq; exact hab (List.cons.inj heq).2
    · apply List.Pairwise.imp _ (choices_nodup lo s)
      intro r t hrt a ha b hb heq
      rcases List.mem_map.mp ha with ⟨us, _, rfl⟩
      rcases List.mem_map.mp hb with ⟨vs, _, rfl⟩
      exact hrt (List.cons.inj heq).1
    · intro a ha b hb heq
      rcases List.mem_map.mp ha with ⟨us, _, rfl⟩
      rcases List.mem_flatMap.mp hb with ⟨r, hr, hb⟩
      rcases List.mem_map.mp hb with ⟨vs, _, rfl⟩
      have hrank := ((choices_iff lo s r).mp hr).2.1
      have he := (List.cons.inj heq).1
      omega

def ordinarySlots : List Slot := [.blackPawn, .whitePawn]
def goBetweenSlots : List Slot := [.blackPawn, .other, .other, .whitePawn]
def lanceSlots : List Slot := [.other, .other, .blackPawn, .whitePawn, .other, .other]

theorem above_zero (slots : List Slot) (u : List Nat) (_h : Admissible slots u) :
    Above 0 u := by
  intro r _
  omega

/-- Complete and duplicate-free enumeration of the independent predicate. -/
theorem exact_enumeration (slots : List Slot) :
    (enumerate 0 slots).Nodup ∧
    (∀ u, u ∈ enumerate 0 slots ↔ Admissible slots u) := by
  refine ⟨enumerate_nodup _ _, ?_⟩
  intro u
  rw [enumerate_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, above_zero slots u h⟩⟩

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

theorem ordinary_length : (enumerate 0 ordinarySlots).length = 34 := by decide
theorem goBetween_length : (enumerate 0 goBetweenSlots).length = 491 := by decide
theorem lance_length : (enumerate 0 lanceSlots).length = 13580 := by decide

/-- Actual bijective cardinality statement, not only an output-list length. -/
theorem goBetween_exact :
    ∃ f : Fin 491 → List Nat,
      (∀ i, Admissible goBetweenSlots (f i)) ∧
      (∀ i j, f i = f j → i = j) ∧
      (∀ u, Admissible goBetweenSlots u → ∃ i, f i = u) :=
  Indexing.exact _ _ (exact_enumeration goBetweenSlots).1
    (exact_enumeration goBetweenSlots).2 _ goBetween_length

theorem lance_exact :
    ∃ f : Fin 13580 → List Nat,
      (∀ i, Admissible lanceSlots (f i)) ∧
      (∀ i j, f i = f j → i = j) ∧
      (∀ u, Admissible lanceSlots u → ∃ i, f i = u) :=
  Indexing.exact _ _ (exact_enumeration lanceSlots).1
    (exact_enumeration lanceSlots).2 _ lance_length

end ChuShogi.OrderedFile
