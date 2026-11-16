import ChuShogi.OrderedFile

/-!
Strengthened I5 and existential promotion origins. Origins are witnesses, not
part of a canonical Board or a multiplicative factor in its count.
-/
namespace ChuShogi.Promotion

inductive Colour where
  | black | white
  deriving DecidableEq, Repr

inductive Kind where
  | pawn | lance | chariot | goBetween
  deriving DecidableEq, Repr

abbrev UFile := Colour → Kind → Nat

def opposite : Colour → Colour
  | .black => .white
  | .white => .black

/-- White is evaluated in its own reflected coordinates; absence stays zero. -/
def ownRank (c : Colour) (r : Nat) : Nat :=
  if r = 0 then 0 else match c with
    | .black => r
    | .white => 13 - r

/-- Hand-written strengthened I5, including the absent supplying slot. -/
def Eligible (u : UFile) (c : Colour) (k : Kind) : Prop :=
  u c k = 0 ∧
  match k with
  | .pawn => u (opposite c) .pawn = 0
  | .goBetween => u (opposite c) .pawn = 0
  | .chariot => u (opposite c) .pawn = 0 ∧
      (u c .pawn = 0 ∨ 10 ≤ ownRank c (u c .pawn))
  | .lance => u (opposite c) .pawn = 0 ∧
      ¬ (u c .chariot ≠ 0 ∧ u c .pawn ≠ 0 ∧
         u (opposite c) .chariot ≠ 0 ∧ u (opposite c) .lance ≠ 0) ∧
      (u c .pawn = 0 ∨
        10 + (if u c .chariot = 0 then 0 else 1) ≤ ownRank c (u c .pawn))

instance (u : UFile) (c : Colour) (k : Kind) : Decidable (Eligible u c k) := by
  unfold Eligible
  cases k <;> infer_instance

theorem eligible_origin_absent (u : UFile) (c : Colour) (k : Kind)
    (h : Eligible u c k) : u c k = 0 := h.1

theorem pawn_eligibility (u : UFile) (c : Colour) :
    Eligible u c .pawn ↔ u .black .pawn = 0 ∧ u .white .pawn = 0 := by
  cases c <;> simp [Eligible, opposite, and_comm]

/-- n current pieces can be supplied by distinct eligible origins. -/
def Supply (origins : List A) (n : Nat) : Prop :=
  ∃ selected : List A, selected.Nodup ∧ selected ⊆ origins ∧ selected.length = n

/-- Existence of origins is exactly a capacity bound, not a count of witnesses. -/
theorem supply_iff (origins : List A) (hn : origins.Nodup) (n : Nat) :
    Supply origins n ↔ n ≤ origins.length := by
  constructor
  · rintro ⟨selected, hs, hsub, rfl⟩
    exact hs.length_le_of_subset hsub
  · intro h
    exact ⟨origins.take n, hn.take, List.take_subset _ _, by simp [List.length_take, Nat.min_eq_left h]⟩

/-- The two pawn colours require disjoint origins from the same eligible files. -/
def JointSupply (origins : List A) (b w : Nat) : Prop :=
  ∃ bs ws : List A, (bs ++ ws).Nodup ∧ bs ++ ws ⊆ origins ∧
    bs.length = b ∧ ws.length = w

theorem jointSupply_iff (origins : List A) (hn : origins.Nodup) (b w : Nat) :
    JointSupply origins b w ↔ b + w ≤ origins.length := by
  constructor
  · rintro ⟨bs, ws, hs, hsub, rfl, rfl⟩
    simpa using hs.length_le_of_subset hsub
  · intro h
    let selected := origins.take (b + w)
    have hslen : selected.length = b + w := by simp [selected, List.length_take, Nat.min_eq_left h]
    refine ⟨selected.take b, selected.drop b, ?_, ?_, ?_, ?_⟩
    · rw [List.take_append_drop]; exact hn.take
    · rw [List.take_append_drop]; exact List.take_subset _ _
    · simp [List.length_take, hslen]
    · simp [List.length_drop, hslen]

/-- Non-pawn types have separate origin pools; pawn colours share one pool. -/
def OriginFeasible (pawnFiles : List A) (nonpawnFiles : Colour → Kind → List A)
    (n : Colour → Kind → Nat) : Prop :=
  JointSupply pawnFiles (n .black .pawn) (n .white .pawn) ∧
  ∀ c k, k ≠ .pawn → Supply (nonpawnFiles c k) (n c k)

def CapacityBounds (pawnFiles : List A) (nonpawnFiles : Colour → Kind → List A)
    (n : Colour → Kind → Nat) : Prop :=
  n .black .pawn + n .white .pawn ≤ pawnFiles.length ∧
  ∀ c k, k ≠ .pawn → n c k ≤ (nonpawnFiles c k).length

theorem originFeasible_iff (pawnFiles : List A) (nonpawnFiles : Colour → Kind → List A)
    (hp : pawnFiles.Nodup) (hn : ∀ c k, (nonpawnFiles c k).Nodup)
    (n : Colour → Kind → Nat) :
    OriginFeasible pawnFiles nonpawnFiles n ↔ CapacityBounds pawnFiles nonpawnFiles n := by
  unfold OriginFeasible CapacityBounds
  rw [jointSupply_iff pawnFiles hp]
  constructor
  · rintro ⟨h, hs⟩
    exact ⟨h, fun c k hk => (supply_iff _ (hn c k) _).mp (hs c k hk)⟩
  · rintro ⟨h, hs⟩
    exact ⟨h, fun c k hk => (supply_iff _ (hn c k) _).mpr (hs c k hk)⟩

/-- Actual original-slot inventory, with file indices 0--11 as in Python. -/
def HasSlot (x : Fin 12) (_c : Colour) : Kind → Prop
  | .pawn => True
  | .lance | .chariot => x.val = 0 ∨ x.val = 11
  | .goBetween => x.val = 3 ∨ x.val = 8

instance (x : Fin 12) (c : Colour) (k : Kind) : Decidable (HasSlot x c k) := by
  cases k <;> unfold HasSlot <;> infer_instance

def pawnFiles (u : Fin 12 → UFile) : List (Fin 12) :=
  (List.finRange 12).filter fun x => decide (u x .black .pawn = 0 ∧ u x .white .pawn = 0)

def nonpawnFiles (u : Fin 12 → UFile) (c : Colour) (k : Kind) : List (Fin 12) :=
  (List.finRange 12).filter fun x => decide (HasSlot x c k ∧ Eligible (u x) c k)

/-- The concrete twelve-file capacity equivalence has no enumeration hypotheses. -/
theorem chu_originFeasible_iff (u : Fin 12 → UFile) (n : Colour → Kind → Nat) :
    OriginFeasible (pawnFiles u) (nonpawnFiles u) n ↔
      CapacityBounds (pawnFiles u) (nonpawnFiles u) n := by
  apply originFeasible_iff
  · exact (List.nodup_finRange 12).filter _
  · intro c k; exact (List.nodup_finRange 12).filter _

/-- A concrete capacity witness never supplies from a still-unpromoted origin. -/
theorem nonpawn_origin_absent (u : Fin 12 → UFile) (c : Colour) (k : Kind)
    (x : Fin 12) (h : x ∈ nonpawnFiles u c k) : u x c k = 0 := by
  have he : HasSlot x c k ∧ Eligible (u x) c k := by
    simpa only [nonpawnFiles, List.mem_filter, decide_eq_true_eq, List.mem_finRange,
      true_and] using h
  exact he.2.1

end ChuShogi.Promotion
