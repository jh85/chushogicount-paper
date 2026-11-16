import ChuShogi.CompletionProfiles

/-! Disjoint free Board functions are exactly words on the two available-square
classes. This representation contains canonical pieces and empty squares only. -/
namespace ChuShogi.ResidualWords
open Specification BoardDecomposition

abbrev Available (u : Board) := {s : Square // u s = none}
abbrev AvailableClass (u : Board) (a : Nat) := {s : Square // u s = none ∧ squareClass s = a}
abbrev Word (u : Board) := Available u → Option Piece
abbrev Words (u : Board) := (AvailableClass u 0 → Option Piece) × (AvailableClass u 1 → Option Piece)

def extend (u : Board) (w : Word u) : Board := fun s => if h : u s = none then w ⟨s,h⟩ else none

def restrict (u f : Board) : Word u := fun s => f s.val

theorem extend_disjoint (u : Board) (w : Word u) : Disjoint u (extend u w) := by
  intro s
  by_cases h : u s = none
  · exact Or.inl h
  · exact Or.inr (by simp [extend,h])

theorem restrict_extend (u : Board) (w : Word u) : restrict u (extend u w) = w := by
  funext s
  simp only [restrict,extend,dite_eq_left s.property]

theorem extend_restrict (u f : Board) (h : Disjoint u f) : extend u (restrict u f) = f := by
  funext s
  by_cases he : u s = none
  · simp [extend,restrict,he]
  · have hf := (h s).resolve_left he
    simp [extend,he,hf]

def split (u : Board) (w : Word u) : Words u :=
  ((fun s => w ⟨s.val,s.property.1⟩),(fun s => w ⟨s.val,s.property.1⟩))

def join (u : Board) (w : Words u) : Word u := fun s =>
  if h : squareClass s.val = 0 then w.1 ⟨s.val,s.property,h⟩
  else w.2 ⟨s.val,s.property,by unfold squareClass at *; omega⟩

theorem join_split (u : Board) (w : Word u) : join u (split u w) = w := by
  funext s
  unfold join split
  split <;> rfl

theorem split_join (u : Board) (w : Words u) : split u (join u w) = w := by
  apply Prod.ext
  · funext s
    change (if h : squareClass s.val = 0 then _ else _) = _
    rw [dite_eq_left s.property.2]
  · funext s
    have hn : squareClass s.val ≠ 0 := by rw [s.property.2]; decide
    change (if h : squareClass s.val = 0 then _ else _) = _
    rw [dite_eq_right hn]

def toBoard (u : Board) (w : Words u) : Board := extend u (join u w)
def fromBoard (u f : Board) : Words u := split u (restrict u f)

theorem from_to (u : Board) (w : Words u) : fromBoard u (toBoard u w) = w := by
  rw [fromBoard,toBoard,restrict_extend,split_join]

theorem to_from (u f : Board) (h : Disjoint u f) : toBoard u (fromBoard u f) = f := by
  rw [toBoard,fromBoard,join_split,extend_restrict u f h]

/-- All availability hypotheses are discharged by extension/restriction. -/
def wordBoardIso (u : Board) : FiniteRelabelling.Iso (Words u) {f : Board // Disjoint u f} where
  forward w := ⟨toBoard u w,extend_disjoint u (join u w)⟩
  backward f := fromBoard u f.val
  left_inverse := from_to u
  right_inverse f := by apply Subtype.ext; exact to_from u f.val f.property

end ChuShogi.ResidualWords
