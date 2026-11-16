import ChuShogi.FiniteBoards

/-! Counting the independent disjoint royal strata gives all candidate Boards.
This is symbolic and does not evaluate the finite Board universe. -/
namespace ChuShogi.CandidatePartition
open Specification FiniteBoards

theorem card_split : card Candidate = card C_r+card C_nr := by
  classical
  have h (xs : List Board) :
      (xs.filter fun b => decide (Candidate b)).length =
        (xs.filter fun b => decide (C_r b)).length+(xs.filter fun b => decide (C_nr b)).length := by
    induction xs with
    | nil => rfl
    | cons b xs ih =>
      by_cases hc : Candidate b <;> by_cases hr : hasRoyal b .black <;>
        simp [C_r,C_nr,hc,hr,ih,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
  unfold card
  rw [subtypeEnum_length,subtypeEnum_length,subtypeEnum_length]
  exact h allBoards

end ChuShogi.CandidatePartition
