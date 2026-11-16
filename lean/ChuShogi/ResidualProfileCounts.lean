import ChuShogi.ResidualWords
import ChuShogi.FiniteBoards
import ChuShogi.MultinomialPlacements

/-! Actual class profiles are exactly role fibres of residual square words.
This connects the concrete Board predicate to multinomial counting. -/
namespace ChuShogi.ResidualProfileCounts
open scoped Classical
open Specification Promotion ConcreteDP BoardDecomposition CompletionProfiles ResidualWords

noncomputable instance optionPieceFintype : Fintype (Option Piece) :=
  Fintype.ofList FiniteBoards.options FiniteBoards.options_complete

noncomputable instance classFintype (u : Board) (a : Nat) : Fintype (AvailableClass u a) := Fintype.ofFinite _

/-- A complete no-duplicate square list and Fintype cardinality agree. -/
theorem square_filter_card (P : Square → Prop) :
    (FiniteBoards.subtypeEnum squares P).length = Nat.card {s // P s} := by
  classical
  let e : FiniteRelabelling.Iso {s // P s} {s // P s} := ⟨id,id,fun _ => rfl,fun _ => rfl⟩
  have hh := FiniteBoards.iso_lengths (FiniteBoards.subtypeEnum squares P)
    (Finset.univ.toList : List {s // P s})
    (FiniteBoards.subtypeEnum_nodup squares Rendering.squares_nodup P) (Finset.nodup_toList _)
    (FiniteBoards.subtypeEnum_complete squares mem_squares P) (by simp) e
  have he : (FiniteBoards.subtypeEnum squares P).length = Fintype.card {s // P s} := by simpa using hh
  exact he.trans Nat.card_eq_fintype_card.symm

theorem profile_card (b : Board) (a : Nat) (c : Colour) (r : Role) :
    profile b a c r = Nat.card {s : Square // b s = some (c,r) ∧ squareClass s = a} := by
  classical
  let P : Square → Prop := fun s => b s = some (c,r) ∧ squareClass s = a
  calc
    profile b a c r = (FiniteBoards.subtypeEnum squares P).length := by
      rw [FiniteBoards.subtypeEnum_length]
      unfold profile countWhere
      apply congrArg List.length
      apply List.filter_congr
      intro s _
      by_cases hp : b s = some (c,r) <;> by_cases ha : squareClass s = a <;> simp [P,hp,ha]
    _ = _ := square_filter_card P

theorem toBoard_available (u : Board) (w : Words u) (s : Square) (p : Piece)
    (h : ResidualWords.toBoard u w s = some p) : u s = none := by
  unfold ResidualWords.toBoard extend at h
  split at h
  · assumption
  · cases h

/-- General fibre identification; word lookup and availability premises are
later discharged for the two actual residual classes. -/
theorem profile_word (u b : Board) (a : Nat) (w : AvailableClass u a → Option Piece)
    (ha : ∀ s p, b s = some p → u s = none)
    (hw : ∀ t : AvailableClass u a, b t.val = w t) (c : Colour) (r : Role) :
    profile b a c r = MultinomialPlacements.multiplicity w (some (c,r)) := by
  classical
  rw [profile_card]
  have hm : Nat.card {t : AvailableClass u a // w t = some (c,r)} =
      MultinomialPlacements.multiplicity w (some (c,r)) := Nat.card_eq_fintype_card
  rw [← hm]
  apply Nat.card_congr
  exact {
    toFun := fun s => ⟨⟨s.val,ha s.val (c,r) s.property.1,s.property.2⟩,by
      rw [← hw]; exact s.property.1⟩
    invFun := fun t => ⟨t.val.val,by rw [hw]; exact t.property,t.val.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem class0_lookup (u : Board) (w : Words u) (t : AvailableClass u 0) :
    ResidualWords.toBoard u w t.val = w.1 t := by
  simp only [ResidualWords.toBoard,extend,dite_eq_left t.property.1,join,dite_eq_left t.property.2]

theorem class1_lookup (u : Board) (w : Words u) (t : AvailableClass u 1) :
    ResidualWords.toBoard u w t.val = w.2 t := by
  have hn : squareClass t.val ≠ 0 := by rw [t.property.2]; decide
  simp only [ResidualWords.toBoard,extend,dite_eq_left t.property.1,join,dite_eq_right hn]

theorem profile0_word (u : Board) (w : Words u) (c : Colour) (r : Role) :
    profile (ResidualWords.toBoard u w) 0 c r = MultinomialPlacements.multiplicity w.1 (some (c,r)) :=
  profile_word u _ 0 w.1 (toBoard_available u w) (class0_lookup u w) c r

theorem profile1_word (u : Board) (w : Words u) (c : Colour) (r : Role) :
    profile (ResidualWords.toBoard u w) 1 c r = MultinomialPlacements.multiplicity w.2 (some (c,r)) :=
  profile_word u _ 1 w.2 (toBoard_available u w) (class1_lookup u w) c r

def someCounts (q : Option Piece → Nat) : Counts := fun c r => q (some (c,r))

def WordConditions (r : Bool) (s : Summary) (q0 q1 : Option Piece → Nat) : Prop :=
  ValidProfile r s (someCounts q0) (someCounts q1)

theorem word_completes (r : Bool) (u : Board) (w : Words u) (hu : OnlyConfined u)
    (h1 : I1 u) (h2 : I2 u) (h3 : I3 u) :
    SummarySufficiency.StratumCompletes r u (ResidualWords.toBoard u w) ↔
      WordConditions r (SummaryBridge.boardSummary u)
        (MultinomialPlacements.multiplicity w.1) (MultinomialPlacements.multiplicity w.2) := by
  have he0 : profile (ResidualWords.toBoard u w) 0 = someCounts (MultinomialPlacements.multiplicity w.1) := by
    funext c p; exact profile0_word u w c p
  have he1 : profile (ResidualWords.toBoard u w) 1 = someCounts (MultinomialPlacements.multiplicity w.2) := by
    funext c p; exact profile1_word u w c p
  rw [completes_profile r u _ hu h1 h2 h3,he0,he1]
  exact and_iff_right (extend_disjoint u (join u w))

/-- Independent arithmetic-profile words and actual completions are bijective. -/
def completionWordIso (r : Bool) (u : Board) (hu : OnlyConfined u) (h1 : I1 u) (h2 : I2 u) (h3 : I3 u) :
    FiniteRelabelling.Iso
      {w : Words u // WordConditions r (SummaryBridge.boardSummary u)
        (MultinomialPlacements.multiplicity w.1) (MultinomialPlacements.multiplicity w.2)}
      {f : Board // SummarySufficiency.StratumCompletes r u f} where
  forward w := ⟨ResidualWords.toBoard u w.val,(word_completes r u w.val hu h1 h2 h3).mpr w.property⟩
  backward f := ⟨ResidualWords.fromBoard u f.val,(word_completes r u _ hu h1 h2 h3).mp
    (by rw [to_from u f.val f.property.2.1]; exact f.property)⟩
  left_inverse w := by apply Subtype.ext; exact from_to u w.val
  right_inverse f := by apply Subtype.ext; exact to_from u f.val f.property.2.1

/-- The independent symbolic Board cardinality agrees with ordinary finite cardinality. -/
theorem board_card (P : Board → Prop) : FiniteBoards.card P = Nat.card {b // P b} := by
  classical
  let e : FiniteRelabelling.Iso {b // P b} {b // P b} := ⟨id,id,fun _ => rfl,fun _ => rfl⟩
  have hh := FiniteBoards.iso_lengths (FiniteBoards.subtypeEnum FiniteBoards.allBoards P)
    (Finset.univ.toList : List {b // P b})
    (FiniteBoards.subtypeEnum_nodup _ FiniteBoards.universe_nodup P) (Finset.nodup_toList _)
    (FiniteBoards.subtypeEnum_complete _ FiniteBoards.universe_complete P) (by simp) e
  have he : (FiniteBoards.subtypeEnum FiniteBoards.allBoards P).length = Fintype.card {b // P b} := by simpa using hh
  exact he.trans Nat.card_eq_fintype_card.symm

noncomputable def profileFormula (r : Bool) (u : Board) : Nat :=
  ∑ p : MultinomialPlacements.Profiles (S := AvailableClass u 0) (R := Option Piece),
    ∑ q : MultinomialPlacements.Profiles (S := AvailableClass u 1) (R := Option Piece),
      Nat.multinomial Finset.univ p.val * Nat.multinomial Finset.univ q.val *
        (if WordConditions r (SummaryBridge.boardSummary u) p.val q.val then 1 else 0)

/-- Concrete completion profile formula, with all Board/word/fibre hypotheses
proved. This profile sum still needs efficient group/EGF evaluation. -/
theorem completion_profile_formula (r : Bool) (u : Board) (hu : OnlyConfined u)
    (h1 : I1 u) (h2 : I2 u) (h3 : I3 u) :
    FiniteBoards.card (SummarySufficiency.StratumCompletes r u) = profileFormula r u := by
  classical
  rw [board_card]
  have e := completionWordIso r u hu h1 h2 h3
  let eqv := Equiv.mk e.forward e.backward e.left_inverse e.right_inverse
  rw [← Nat.card_congr eqv,Nat.card_eq_fintype_card]
  have hc : Fintype.card {w : Words u // WordConditions r (SummaryBridge.boardSummary u)
      (MultinomialPlacements.multiplicity w.1) (MultinomialPlacements.multiplicity w.2)} =
      ∑ w : Words u, if WordConditions r (SummaryBridge.boardSummary u)
        (MultinomialPlacements.multiplicity w.1) (MultinomialPlacements.multiplicity w.2) then 1 else 0 := by
    rw [Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [hc,Fintype.sum_prod_type]
  exact MultinomialPlacements.two_class_weighted_sum (S := AvailableClass u 0) (T := AvailableClass u 1)
    (R := Option Piece) (fun m n => if WordConditions r (SummaryBridge.boardSummary u) m n then 1 else 0)

end ChuShogi.ResidualProfileCounts

