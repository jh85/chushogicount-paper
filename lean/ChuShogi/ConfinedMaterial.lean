import ChuShogi.OccupancyBridge

/-! Confined material bounds are implied by slot uniqueness and origin capacity.
This explains why the concrete summary need not retain unpromoted type counts. -/
namespace ChuShogi.ConfinedMaterial
open Specification Promotion ConcreteDP BoardDecomposition SummaryBridge OccupancyBridge

theorem slot_length_bit (b : Board) (hb : I1 b) (x : Fin 12) (c : Colour) (k : Kind) :
    (slotSquares b x c k).length = bit (unpromoted b x c k ≠ 0) := by
  by_cases hz : unpromoted b x c k = 0
  · simp [slot_empty b hb x c k hz,bit,hz]
  · obtain ⟨s,hx,hs,_⟩ := unpromoted_present b hb x c k hz
    have hm : s ∈ slotSquares b x c k := by simp [slotSquares,mem_squares,hx,hs]
    have hl : (slotSquares b x c k).length ≤ 1 := by rw [slotSquares_length]; exact hb.2 _ _ _
    rw [singleton_of_short_mem _ hl s hm]
    simp [bit,hz]

/-- File partition of any present canonical role; no I1 assumption is needed. -/
theorem number_by_file (b : Board) (c : Colour) (r : Role) :
    (indices.map fun x => countWhere b c r (fun s => decide (s.1 = x))).sum = number b c r := by
  have hi (x : Fin 12) : countWhere b c r (fun s => decide (s.1 = x)) =
      (squares.map fun s => bit (x = s.1 ∧ b s = some (c,r))).sum := by
    rw [sum_bits]
    unfold countWhere
    congr 1
    apply List.filter_congr
    intro s _
    by_cases hf : x = s.1 <;> by_cases hp : b s = some (c,r) <;> simp_all [eq_comm]
  simp only [hi]
  rw [WeightedDP.sum_exchange]
  simp only [sum_indicator _ (by decide : indices.Nodup)]
  have hmap : (fun s : Square => bit (s.1 ∈ indices ∧ b s = some (c,r))) =
      (fun s => bit (b s = some (c,r))) := by
    funext s
    simp [indices]
  rw [hmap,sum_bits]
  simp only [number,countWhere,Bool.and_true]

theorem native_count (b : Board) (hb : I1 b) (c : Colour) (k : Kind) :
    number b c (.native (kindBase k)) =
      (indices.map fun x => bit (unpromoted b x c k ≠ 0)).sum := by
  rw [← number_by_file]
  congr 1
  apply List.map_congr_left
  intro x _
  rw [← slotSquares_length,slot_length_bit b hb]

theorem local_material_bound (b : Board) (hb : I1 b) (x : Fin 12) (c : Colour) (k : Kind) :
    bit (unpromoted b x c k ≠ 0) +
      bit (HasSlot x c k ∧ Eligible (unpromoted b x) c k) ≤ bit (HasSlot x c k) := by
  by_cases hs : HasSlot x c k
  · by_cases hz : unpromoted b x c k = 0
    · by_cases he : Eligible (unpromoted b x) c k <;> simp [bit,hs,hz,he]
    · have he : ¬ Eligible (unpromoted b x) c k := fun h => hz h.1
      simp [bit,hs,hz,he]
  · have hz := absent_slot_zero b hb x c k hs
    simp [bit,hs,hz]

def stock (k : Kind) : Nat := if k = .pawn then 12 else 2

theorem slot_stock (c : Colour) (k : Kind) :
    (indices.filter fun x => decide (HasSlot x c k)).length = stock k := by
  cases c <;> cases k <;> decide

/-- Unpromoted pieces and all eligible origins together fit the initial stock. -/
theorem native_capacity_bound (b : Board) (hb : I1 b) (c : Colour) (k : Kind) :
    number b c (.native (kindBase k)) + (nonpawnFiles (unpromoted b) c k).length ≤ stock k := by
  rw [native_count b hb]
  have hcap : (nonpawnFiles (unpromoted b) c k).length =
      (indices.map fun x => bit (HasSlot x c k ∧ Eligible (unpromoted b x) c k)).sum := by
    rw [sum_bits]
    simp [indices,nonpawnFiles,List.filter_reverse]
  rw [hcap]
  rw [← WeightedDP.sum_add]
  have hi (xs : List (Fin 12)) :
      (xs.map fun x => bit (unpromoted b x c k ≠ 0) +
        bit (HasSlot x c k ∧ Eligible (unpromoted b x) c k)).sum ≤
      (xs.map fun x => bit (HasSlot x c k)).sum := by
    induction xs with
    | nil => exact Nat.le_refl _
    | cons x xs ih =>
      simp only [List.map_cons,List.sum_cons]
      have hh := local_material_bound b hb x c k
      omega
  have hh := hi indices
  rw [sum_bits,slot_stock] at hh
  exact hh

theorem pawn_pool_eq (b : Board) (c : Colour) :
    nonpawnFiles (unpromoted b) c .pawn = pawnFiles (unpromoted b) := by
  unfold nonpawnFiles pawnFiles
  congr 1
  funext x
  simp [HasSlot,pawn_eligibility]

/-- Every confined I9 inequality follows from the independently intended I1/I4/I5. -/
theorem confined_material (b : Board) (h1 : I1 b) (h4 : I4 b) (h5 : I5 b)
    (c : Colour) (k : Kind) :
    number b c (.native (kindBase k)) + promotedNumber b c k ≤ stock k := by
  have hb := native_capacity_bound b h1 c k
  by_cases hk : k = .pawn
  · subst k
    rw [pawn_pool_eq b c] at hb
    have hn : promotedNumber b c .pawn ≤ (pawnFiles (unpromoted b)).length := by
      cases c <;> unfold I4 at h4 <;> omega
    omega
  · have hn := h5 c k hk
    omega

end ChuShogi.ConfinedMaterial
