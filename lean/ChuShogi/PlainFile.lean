import Std

/-!
# The ordinary-file milestone

This module counts only the surviving unpromoted Black and White pawns on one
fixed ordinary file. It does not count other pieces, promotion/capture histories,
the complete abstract file game, or reachable chu-shogi positions.

`Rank` uses zero-based storage; `displayedRank` is the manuscript's rank 1--12.
The declarative predicate `Admissible` is independent of `enumeration`.
-/

namespace ChuShogi.PlainFile

abbrev Rank := Fin 12

/-- Optional ranks of the Black pawn and the White pawn, respectively. -/
abbrev Config := Option Rank × Option Rank

def displayedRank (r : Rank) : Nat := r.val + 1

/--
I1 is implicit in the fixed-file representation. I2 requires the surviving
Black pawn to precede the White pawn. I3 gives Black rank >= 4 and White rank <= 9.
Last-rank pawns are permitted: Black on 12 and White on 1 are not excluded.
-/
def Admissible : Config → Prop
  | (none, none) => True
  | (some b, none) => 4 ≤ displayedRank b
  | (none, some w) => displayedRank w ≤ 9
  | (some b, some w) =>
      4 ≤ displayedRank b ∧ displayedRank w ≤ 9 ∧ displayedRank b < displayedRank w

instance (c : Config) : Decidable (Admissible c) :=
  match c with
  | (none, none) => inferInstanceAs (Decidable True)
  | (some b, none) => inferInstanceAs (Decidable (4 ≤ displayedRank b))
  | (none, some w) => inferInstanceAs (Decidable (displayedRank w ≤ 9))
  | (some b, some w) => inferInstanceAs
      (Decidable (4 ≤ displayedRank b ∧ displayedRank w ≤ 9 ∧
        displayedRank b < displayedRank w))

/-- The nine possible ranks 4--12 for a lone Black pawn. -/
def blackRanks : List Rank :=
  (List.finRange 9).map fun r => ⟨r.val + 3, by omega⟩

/-- The nine possible ranks 1--9 for a lone White pawn. -/
def whiteRanks : List Rank :=
  (List.finRange 9).map fun r => ⟨r.val, by omega⟩

/-- When both pawns survive, both ranks lie in 4--9. -/
def sharedRanks : List Rank :=
  (List.finRange 6).map fun r => ⟨r.val + 3, by omega⟩

def neither : List Config := [(none, none)]

def blackOnly : List Config :=
  blackRanks.map fun b => (some b, none)

def whiteOnly : List Config :=
  whiteRanks.map fun w => (none, some w)

/-- Explicitly choose an ordered pair of different ranks in 4--9. -/
def both : List Config :=
  sharedRanks.flatMap fun b =>
    (sharedRanks.filter fun w => decide (b.val < w.val)).map fun w =>
      (some b, some w)

/-- Four disjoint cases; this definition does not call `Admissible`. -/
def enumeration : List Config :=
  neither ++ blackOnly ++ whiteOnly ++ both

set_option maxRecDepth 4096
set_option maxHeartbeats 10000000

theorem neither_length : neither.length = 1 := by decide
theorem blackOnly_length : blackOnly.length = 9 := by decide
theorem whiteOnly_length : whiteOnly.length = 9 := by decide
theorem both_length : both.length = 15 := by decide

/-- The actual list, rather than a deduplicated set, contains no repetitions. -/
theorem enumeration_nodup : enumeration.Nodup := by decide

theorem enumeration_length : enumeration.length = 34 := by decide

/-- Every configuration appears exactly when the independent specification allows it. -/
theorem enumeration_iff (c : Config) : c ∈ enumeration ↔ Admissible c := by
  cases c with
  | mk b w =>
    cases b with
    | none =>
      cases w with
      | none => decide
      | some w =>
        exact (by decide : ∀ w : Rank,
          (none, some w) ∈ enumeration ↔ Admissible (none, some w)) w
    | some b =>
      cases w with
      | none =>
        exact (by decide : ∀ b : Rank,
          (some b, none) ∈ enumeration ↔ Admissible (some b, none)) b
      | some w =>
        exact (by decide : ∀ b w : Rank,
          (some b, some w) ∈ enumeration ↔ Admissible (some b, some w)) b w

theorem enumeration_sound (c : Config) (h : c ∈ enumeration) : Admissible c :=
  (enumeration_iff c).mp h

theorem enumeration_complete (c : Config) (h : Admissible c) : c ∈ enumeration :=
  (enumeration_iff c).mpr h

/-- An explicit map from the 34 indices to the listed current configurations. -/
def unrank (i : Fin 34) : Config :=
  enumeration[i.val]'(by simpa only [enumeration_length] using i.isLt)

theorem unrank_valid : ∀ i : Fin 34, Admissible (unrank i) := by decide

theorem unrank_injective :
    ∀ i j : Fin 34, unrank i = unrank j → i = j := by decide

theorem unrank_surjective (c : Config) :
    Admissible c → ∃ i : Fin 34, unrank i = c := by
  cases c with
  | mk b w =>
    cases b with
    | none =>
      cases w with
      | none => decide
      | some w =>
        exact (by decide : ∀ w : Rank,
          Admissible (none, some w) →
            ∃ i : Fin 34, unrank i = (none, some w)) w
    | some b =>
      cases w with
      | none =>
        exact (by decide : ∀ b : Rank,
          Admissible (some b, none) →
            ∃ i : Fin 34, unrank i = (some b, none)) b
      | some w =>
        exact (by decide : ∀ b w : Rank,
          Admissible (some b, some w) →
            ∃ i : Fin 34, unrank i = (some b, some w)) b w

/--
Exact cardinality without a Mathlib dependency: `unrank` is a bijection from
`Fin 34` onto precisely the configurations satisfying the independent predicate.
-/
theorem exact_34 :
    (∀ i : Fin 34, Admissible (unrank i)) ∧
    (∀ i j : Fin 34, unrank i = unrank j → i = j) ∧
    (∀ c : Config, Admissible c → ∃ i : Fin 34, unrank i = c) :=
  ⟨unrank_valid, unrank_injective, unrank_surjective⟩

end ChuShogi.PlainFile
