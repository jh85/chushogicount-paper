import ChuShogi.Promotion

/-!
Canonical Boards and I1--I9, independently of any counting algorithm.
There is no side to move or flag in a Board. All predicates use Black-to-move
conventions. I10 is deliberately outside `Candidate`.
-/
namespace ChuShogi.Specification
open Promotion

inductive Base where
  | pawn | lance | chariot | goBetween
  | gold | silver | copper | leopard | tiger | sideMover | verticalMover
  | rook | dragonHorse | dragonKing | bishop
  | elephant | kirin | phoenix | king | lion | freeKing
  deriving DecidableEq, Repr

/-- These promoted forms remain distinct from every native role. -/
inductive Separate where
  | pawn | lance | chariot | goBetween
  | gold | silver | copper | leopard | tiger | sideMover | verticalMover
  | rook | dragonHorse | dragonKing | bishop
  deriving DecidableEq, Repr

def Separate.base : Separate → Base
  | .pawn => .pawn | .lance => .lance | .chariot => .chariot | .goBetween => .goBetween
  | .gold => .gold | .silver => .silver | .copper => .copper | .leopard => .leopard
  | .tiger => .tiger | .sideMover => .sideMover | .verticalMover => .verticalMover
  | .rook => .rook | .dragonHorse => .dragonHorse | .dragonKing => .dragonKing
  | .bishop => .bishop

inductive Role where
  | native (base : Base)
  | promoted (base : Separate)
  deriving DecidableEq, Repr

/-- Only these three promotions merge with native identities. -/
def promote : Base → Option Role
  | .pawn => some (.promoted .pawn) | .lance => some (.promoted .lance)
  | .chariot => some (.promoted .chariot) | .goBetween => some (.promoted .goBetween)
  | .gold => some (.promoted .gold) | .silver => some (.promoted .silver)
  | .copper => some (.promoted .copper) | .leopard => some (.promoted .leopard)
  | .tiger => some (.promoted .tiger) | .sideMover => some (.promoted .sideMover)
  | .verticalMover => some (.promoted .verticalMover) | .rook => some (.promoted .rook)
  | .dragonHorse => some (.promoted .dragonHorse)
  | .dragonKing => some (.promoted .dragonKing) | .bishop => some (.promoted .bishop)
  | .elephant => some (.native .king) | .kirin => some (.native .lion)
  | .phoenix => some (.native .freeKing)
  | .king | .lion | .freeKing => none

abbrev Square := Fin 12 × Fin 12
abbrev Piece := Colour × Role
abbrev Board := Square → Option Piece

def squares : List Square :=
  (List.finRange 12).flatMap fun x => (List.finRange 12).map fun r => (x, r)

def rank (s : Square) : Nat := s.2.val + 1
def squareClass (s : Square) : Nat := (s.1.val + rank s) % 2

def countWhere (b : Board) (c : Colour) (role : Role) (p : Square → Bool) : Nat :=
  (squares.filter fun s => decide (b s = some (c, role)) && p s).length

def number (b : Board) (c : Colour) (role : Role) : Nat := countWhere b c role (fun _ => true)

def kindBase : Kind → Base
  | .pawn => .pawn | .lance => .lance | .chariot => .chariot | .goBetween => .goBetween

def kindSeparate : Kind → Separate
  | .pawn => .pawn | .lance => .lance | .chariot => .chariot | .goBetween => .goBetween

def confinedStart (c : Colour) (k : Kind) : Nat :=
  match c, k with
  | .black, .lance => 1 | .black, .chariot => 2
  | .black, .pawn => 4 | .black, .goBetween => 5
  | .white, .goBetween => 8 | .white, .pawn => 9
  | .white, .chariot => 11 | .white, .lance => 12

/-- I1: original files, with no two current unpromoted pieces claiming one slot. -/
def I1 (b : Board) : Prop :=
  (∀ s c k, b s = some (c, .native (kindBase k)) → HasSlot s.1 c k) ∧
  ∀ x c k, countWhere b c (.native (kindBase k)) (fun s => decide (s.1 = x)) ≤ 1

/-- I2: strict order of surviving slots on their file. -/
def I2 (b : Board) : Prop :=
  ∀ s t c d k l,
    b s = some (c, .native (kindBase k)) → b t = some (d, .native (kindBase l)) →
    s.1 = t.1 → confinedStart c k < confinedStart d l → rank s < rank t

def I3 (b : Board) : Prop :=
  (∀ s, b s = some (.black, .native .pawn) → 4 ≤ rank s) ∧
  (∀ s, b s = some (.white, .native .pawn) → rank s ≤ 9)

/-- Rank of a slot, or zero when absent. Under I1 at most one summand is nonzero. -/
def unpromoted (b : Board) (x : Fin 12) : UFile := fun c k =>
  ((squares.filter fun s => decide (s.1 = x ∧ b s = some (c, .native (kindBase k)))).map rank).sum

def promotedNumber (b : Board) (c : Colour) (k : Kind) : Nat :=
  number b c (.promoted (kindSeparate k))

def I4 (b : Board) : Prop :=
  promotedNumber b .black .pawn + promotedNumber b .white .pawn ≤
    (pawnFiles (unpromoted b)).length

/-- Strengthened origin condition; an unpromoted origin is unavailable. -/
def I5 (b : Board) : Prop :=
  ∀ c k, k ≠ .pawn → promotedNumber b c k ≤ (nonpawnFiles (unpromoted b) c k).length

/-- Two native bishops cannot both lie in one square colour class. -/
def I6 (b : Board) : Prop :=
  ∀ c a, a < 2 → countWhere b c (.native .bishop) (fun s => decide (squareClass s = a)) ≤ 1

def I7 (b : Board) : Prop :=
  ∀ s c, b s = some (c, .native .kirin) → squareClass s = 1

def hasRoyal (b : Board) (c : Colour) : Prop := 0 < number b c (.native .king)
def I8 (b : Board) : Prop := hasRoyal b .white

def initialSeparate : Separate → Nat
  | .pawn => 12
  | _ => 2

/-- Material limits stated on canonical roles, without choosing their origins. -/
def I9 (b : Board) : Prop :=
  ∀ c,
    (∀ k : Separate, number b c (.native k.base) + number b c (.promoted k) ≤ initialSeparate k) ∧
    number b c (.native .elephant) ≤ 1 ∧
    number b c (.native .king) + number b c (.native .elephant) ≤ 2 ∧
    number b c (.native .kirin) ≤ 1 ∧
    number b c (.native .kirin) + number b c (.native .lion) ≤ 2 ∧
    number b c (.native .phoenix) ≤ 1 ∧
    number b c (.native .phoenix) + number b c (.native .freeKing) ≤ 2

def Candidate (b : Board) : Prop :=
  I1 b ∧ I2 b ∧ I3 b ∧ I4 b ∧ I5 b ∧ I6 b ∧ I7 b ∧ I8 b ∧ I9 b

def C_r (b : Board) : Prop := Candidate b ∧ hasRoyal b .black
def C_nr (b : Board) : Prop := Candidate b ∧ ¬ hasRoyal b .black

theorem candidate_royal_partition (b : Board) :
    Candidate b ↔ C_r b ∨ C_nr b := by
  unfold C_r C_nr
  by_cases h : hasRoyal b .black <;> simp [h]

theorem royal_strata_disjoint (b : Board) : ¬ (C_r b ∧ C_nr b) := by
  intro h
  exact h.2.2 h.1.2

/-- I4 and strengthened I5 exactly express existential promotion-origin capacity. -/
theorem promotion_origins_iff (b : Board) :
    I4 b ∧ I5 b ↔ OriginFeasible (pawnFiles (unpromoted b))
      (nonpawnFiles (unpromoted b)) (promotedNumber b) :=
  (chu_originFeasible_iff (unpromoted b) (promotedNumber b)).symm

end ChuShogi.Specification
