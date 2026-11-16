import ChuShogi.ResidualSquares

/-! Double counting connects the actual confined Board occupancy to d0/d1. -/
namespace ChuShogi.OccupancyBridge
open Specification Promotion ConcreteDP BoardDecomposition SummaryBridge ResidualSquares

theorem sum_zero {A : Type} (xs : List A) : (xs.map fun _ => (0 : Nat)).sum = 0 := by
  induction xs <;> simp_all

theorem sum_indicator {A : Type} [DecidableEq A] (xs : List A) (hn : xs.Nodup)
    (a : A) (p : Prop) [Decidable p] :
    (xs.map fun x => bit (x = a ∧ p)).sum = bit (a ∈ xs ∧ p) := by
  induction xs with
  | nil => simp [bit]
  | cons x xs ih =>
    have hh := List.nodup_cons.mp hn
    simp only [List.map_cons,List.sum_cons]
    rw [ih hh.2]
    by_cases he : x = a
    · subst x
      simp [bit,hh.1]
    · by_cases hp : p <;> simp [bit,he,hp,Ne.symm he,List.mem_cons]

theorem slot_empty (b : Board) (hb : I1 b) (x : Fin 12) (c : Colour) (k : Kind)
    (hz : unpromoted b x c k = 0) : slotSquares b x c k = [] := by
  cases he : slotSquares b x c k with
  | nil => rfl
  | cons s ss =>
    have hm : s ∈ slotSquares b x c k := by rw [he]; simp
    have hs : s.1 = x ∧ b s = some (c,.native (kindBase k)) :=
      of_decide_eq_true (List.mem_filter.mp hm).2
    have hr := unpromoted_at b hb s c k hs.2
    rw [hs.1,hz] at hr
    unfold rank at hr
    omega

def slotCount (b : Board) (x : Fin 12) (l : Label) (a : Nat) : Nat :=
  ((slotSquares b x l.1 l.2).filter fun s => decide (squareClass s = a)).length

theorem slotCount_eq (b : Board) (hb : I1 b) (x : Fin 12) (l : Label) (a : Nat) :
    slotCount b x l a = bit (unpromoted b x l.1 l.2 ≠ 0 ∧
      (x.val + unpromoted b x l.1 l.2) % 2 = a) := by
  by_cases hz : unpromoted b x l.1 l.2 = 0
  · simp [slotCount,slot_empty b hb x l.1 l.2 hz,hz,bit]
  · obtain ⟨s,hx,hs,hr⟩ := unpromoted_present b hb x l.1 l.2 hz
    have hm : s ∈ slotSquares b x l.1 l.2 := by simp [slotSquares,mem_squares,hx,hs]
    have hl : (slotSquares b x l.1 l.2).length ≤ 1 := by
      rw [slotSquares_length]; exact hb.2 _ _ _
    have he := singleton_of_short_mem _ hl s hm
    unfold slotCount
    rw [he]
    rw [hr]
    have hn : rank s ≠ 0 := by unfold rank; omega
    simp only [bit]
    have hclass : (x.val + rank s) % 2 = squareClass s := by simp [← hx,squareClass]
    rw [hclass]
    by_cases ha : squareClass s = a <;> simp [ha]
    exact hn

theorem local_occupied (b : Board) (hb : I1 b) (x : Fin 12) (a : Nat) :
    occupied (boardLocal b x) a = ((labels x).map fun l => slotCount b x l a).sum := by
  unfold occupied
  rw [← sum_bits]
  simp only [boardLocal,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro l _
  exact (slotCount_eq b hb x l a).symm

/-- A per-slot square count is also a sum of independent square indicators. -/
theorem slotCount_sum (b : Board) (x : Fin 12) (l : Label) (a : Nat) :
    slotCount b x l a = (squares.map fun s =>
      bit (s.1 = x ∧ b s = some (Rendering.labelPiece l) ∧ squareClass s = a)).sum := by
  rw [sum_bits]
  unfold slotCount slotSquares
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro s _
  by_cases hf : s.1 = x <;>
    by_cases hp : b s = some (Rendering.labelPiece l) <;>
    by_cases ha : squareClass s = a <;> simp_all [Rendering.labelPiece]

/-- Each occupied confined square contributes exactly once over all original slots. -/
theorem square_indicator (b : Board) (hb : I1 b) (hc : OnlyConfined b) (s : Square) (a : Nat) :
    (indices.map fun x => ((labels x).map fun l =>
      bit (s.1 = x ∧ b s = some (Rendering.labelPiece l) ∧ squareClass s = a)).sum).sum =
    bit (b s ≠ none ∧ squareClass s = a) := by
  cases hs : b s with
  | none => simp [bit,sum_zero]
  | some p =>
    obtain ⟨k,hk⟩ := (isConfined_iff p.2).mp (hc s p hs)
    have hp : b s = some (Rendering.labelPiece (p.1,k)) := by simpa [Rendering.labelPiece,← hk] using hs
    have hm : (p.1,k) ∈ labels s.1 := (labels_membership _ _ _).mpr (hb.1 s p.1 k hp)
    have inner (x : Fin 12) :
        ((labels x).map fun l => bit (s.1 = x ∧ b s = some (Rendering.labelPiece l) ∧ squareClass s = a)).sum =
          bit (x = s.1 ∧ squareClass s = a) := by
      have he (l : Label) : b s = some (Rendering.labelPiece l) ↔ l = (p.1,k) := by
        rw [hp]
        constructor
        · intro h; exact (Rendering.labelPiece_injective _ _ (Option.some.inj h)).symm
        · intro h; rw [h]
      simp only [he]
      have hr : (fun l : Label => bit (s.1 = x ∧ l = (p.1,k) ∧ squareClass s = a)) =
          (fun l => bit (l = (p.1,k) ∧ (s.1 = x ∧ squareClass s = a))) := by
        funext l; congr 1; exact propext (by constructor <;> rintro ⟨h1,h2,h3⟩ <;> exact ⟨h2,h1,h3⟩)
      rw [hr,sum_indicator _ (labels_nodup x)]
      by_cases hx : x = s.1
      · subst x; simp [hm]
      · simp [hx,Ne.symm hx,bit]
    simp only [hs] at inner
    simp only [inner]
    rw [sum_indicator _ (by decide : indices.Nodup)]
    simp [indices,bit]

/-- Double-counting identity for actual canonical confined placements. -/
theorem occupied_sum (b : Board) (hb : I1 b) (hc : OnlyConfined b) (a : Nat) :
    (indices.map fun x => occupied (boardLocal b x) a).sum = occupiedCount b a := by
  simp only [local_occupied b hb]
  simp only [slotCount_sum]
  conv => lhs; arg 1; arg 1; ext x; rw [WeightedDP.sum_exchange]
  rw [WeightedDP.sum_exchange]
  simp only [square_indicator b hb hc]
  exact sum_bits _ _

def occupiedField (s : Summary) (a : Nat) : Nat := if a = 0 then s.d0 else s.d1

theorem summary_occupied (us : List Local) (a : Nat) (ha : a < 2) :
    occupiedField (summary us) a = (us.map fun u => occupied u a).sum := by
  have hz : a = 0 ∨ a = 1 := by omega
  rcases hz with rfl | rfl
  all_goals
    induction us with
    | nil => rfl
    | cons u us ih =>
      change occupiedField (add (summary us) (feature u)) _ = _
      simp only [occupiedField,add,feature] at ih ⊢
      simp only [ite_true,ite_false,Nat.one_ne_zero,List.map_cons,List.sum_cons] at ih ⊢
      omega

theorem boardSummary_occupied (b : Board) (hb : I1 b) (hc : OnlyConfined b) (a : Nat) (ha : a < 2) :
    occupiedField (boardSummary b) a = occupiedCount b a := by
  rw [boardSummary,summary_occupied _ a ha]
  simp only [boardTuple,List.map_map,Function.comp_def]
  exact occupied_sum b hb hc a

theorem occupied_high (b : Board) (a : Nat) (ha : 2 ≤ a) : occupiedCount b a = 0 := by
  unfold occupiedCount
  have he : (squares.filter fun s => decide (b s ≠ none ∧ squareClass s = a)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro s _
    have hs : squareClass s ≠ a := by unfold squareClass; omega
    simp [hs]
  rw [he]
  rfl

/-- Equality of the actual concrete summary constructs the required square bijection. -/
def of_summary (b d : Board) (hb : I1 b) (hd : I1 d)
    (hbc : OnlyConfined b) (hdc : OnlyConfined d) (he : boardSummary b = boardSummary d) :
    ResidualSquares.Relabelling b d := by
  apply ResidualSquares.of_occupied_counts
  intro a
  by_cases ha : a < 2
  · rw [← boardSummary_occupied b hb hbc a ha,← boardSummary_occupied d hd hdc a ha,he]
  · rw [occupied_high b a (by omega),occupied_high d a (by omega)]

end ChuShogi.OccupancyBridge

