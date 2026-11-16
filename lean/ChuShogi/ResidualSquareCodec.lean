import ChuShogi.CompletionWordCodec

/-! Actual residual squares are ordered by a complete filtered list of the
144 squares. This computable relabelling discharges class-size and word-profile
coverage for completion decoding, without a Board-universe enumeration. -/
namespace ChuShogi.ResidualSquareCodec
open Specification BoardDecomposition SummaryBridge ResidualWords CompletionProfiles CanonicalWordProfiles

def positions (u : Board) (a : Nat) : List (AvailableClass u a) :=
  FiniteListEquivalence.subtypeEntries squares (fun s => u s=none ∧ squareClass s=a)

theorem positions_nodup (u : Board) (a : Nat) : (positions u a).Nodup :=
  FiniteListEquivalence.subtypeEntries_nodup _ Rendering.squares_nodup _
theorem positions_complete (u : Board) (a : Nat) (s : AvailableClass u a) : s ∈ positions u a :=
  FiniteListEquivalence.subtypeEntries_complete _ mem_squares _ s

def listEquivalence (u : Board) (a : Nat) : Fin (positions u a).length ≃ AvailableClass u a :=
  FiniteListEquivalence.equivalence (positions u a) (positions_nodup u a) (positions_complete u a)

theorem positions_length (u : Board) (hu : OnlyConfined u) (h1 : I1 u) (a : Nat) (ha : a<2) :
    (positions u a).length=72-OccupancyBridge.occupiedField (boardSummary u) a := by
  have he := Fintype.card_congr (listEquivalence u a)
  simpa only [Fintype.card_fin,ConfigurationWeight.remaining_card u hu h1 a ha] using he

def equivalence (u : Board) (hu : OnlyConfined u) (h1 : I1 u) (a : Nat) (ha : a<2) :
    Fin (72-OccupancyBridge.occupiedField (boardSummary u) a) ≃ AvailableClass u a :=
  (finCongr (positions_length u hu h1 a ha).symm).trans (listEquivalence u a)

def functionEquivalence {S T A : Type} (e : S ≃ T) : (S → A) ≃ (T → A) where
  toFun w t := w (e.symm t)
  invFun w s := w (e s)
  left_inv w := by funext s; simp
  right_inv w := by funext t; simp

def wordsEquivalence (u : Board) (hu : OnlyConfined u) (h1 : I1 u) :
    ((Fin (72-(boardSummary u).d0) → Option Piece) × (Fin (72-(boardSummary u).d1) → Option Piece)) ≃ Words u :=
  Equiv.prodCongr (functionEquivalence (equivalence u hu h1 0 (by decide)))
    (functionEquivalence (equivalence u hu h1 1 (by decide)))

theorem words_profiles (u : Board) (hu : OnlyConfined u) (h1 : I1 u)
    (w : (Fin (72-(boardSummary u).d0) → Option Piece) × (Fin (72-(boardSummary u).d1) → Option Piece)) :
    wordCounts ((wordsEquivalence u hu h1 w).1)=wordCounts w.1 ∧
      wordCounts ((wordsEquivalence u hu h1 w).2)=wordCounts w.2 := by
  constructor <;> funext c r
  · exact ResidualFinCodec.multiplicity_domain (equivalence u hu h1 0 (by decide)) w.1 (some (c,r))
  · exact ResidualFinCodec.multiplicity_domain (equivalence u hu h1 1 (by decide)) w.2 (some (c,r))

def profileEquivalence (r : Bool) (u : Board) (hu : OnlyConfined u) (h1 : I1 u) :
    {w : (Fin (72-(boardSummary u).d0) → Option Piece) × (Fin (72-(boardSummary u).d1) → Option Piece) //
      ValidProfile r (boardSummary u) (wordCounts w.1) (wordCounts w.2)} ≃
    {w : Words u // ResidualProfileCounts.WordConditions r (boardSummary u)
      (MultinomialPlacements.multiplicity w.1) (MultinomialPlacements.multiplicity w.2)} :=
  Equiv.subtypeEquiv (wordsEquivalence u hu h1) (fun w => by
    change ValidProfile r (boardSummary u) (wordCounts w.1) (wordCounts w.2) ↔
      ValidProfile r (boardSummary u) (wordCounts ((wordsEquivalence u hu h1 w).1))
        (wordCounts ((wordsEquivalence u hu h1 w).2))
    rw [(words_profiles u hu h1 w).1,(words_profiles u hu h1 w).2])

end ChuShogi.ResidualSquareCodec
