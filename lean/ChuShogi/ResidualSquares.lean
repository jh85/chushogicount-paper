import ChuShogi.FiniteRelabelling
import ChuShogi.Rendering

/-! Concrete class-preserving square permutations between confined placements.
The permutation exists whenever occupied counts agree in each square class. -/
namespace ChuShogi.ResidualSquares
open Specification BoardDecomposition Placement

def occupiedCount (b : Board) (a : Nat) : Nat :=
  (squares.filter fun s => decide (b s ≠ none ∧ squareClass s = a)).length

def availableCount (b : Board) (a : Nat) : Nat :=
  (squares.filter fun s => decide (b s = none ∧ squareClass s = a)).length

theorem partition_count (b : Board) (a : Nat) :
    availableCount b a + occupiedCount b a =
      (squares.filter fun s => decide (squareClass s = a)).length := by
  have general (xs : List Square) :
      (xs.filter fun s => decide (b s = none ∧ squareClass s = a)).length +
      (xs.filter fun s => decide (b s ≠ none ∧ squareClass s = a)).length =
      (xs.filter fun s => decide (squareClass s = a)).length := by
    induction xs with
    | nil => rfl
    | cons s xs ih =>
      simp only [List.filter_cons]
      by_cases hb : b s = none <;> by_cases ha : squareClass s = a <;>
        simp [hb,ha] at ih ⊢ <;> omega
  exact general squares

def key (b : Board) (s : Square) : Bool × Nat := (decide (b s = none),squareClass s)

theorem key_block (b : Board) (a : Nat) (p : Bool) :
    (FiniteRelabelling.block squares (key b) (p,a)).length =
      if p then availableCount b a else occupiedCount b a := by
  cases p
  · unfold FiniteRelabelling.block occupiedCount
    congr 1 <;> first | rfl | (apply List.filter_congr; intro s _; simp [key])
  · unfold FiniteRelabelling.block availableCount
    congr 1 <;> first | rfl | (apply List.filter_congr; intro s _; simp [key])

structure Relabelling (u v : Board) extends Placement.Relabelling squareClass squareClass where
  preserves_available : ∀ s, v (forward s) = none ↔ u s = none

/-- The required concrete square bijection is constructed, not hypothesized. -/
def of_occupied_counts (u v : Board) (h : ∀ a, occupiedCount u a = occupiedCount v a) :
    Relabelling u v := by
  have hb (a : Nat) : availableCount u a = availableCount v a := by
    have hu := partition_count u a
    have hv := partition_count v a
    have hh := h a
    omega
  have he (a : Bool × Nat) :
      (FiniteRelabelling.block squares (key u) a).length =
        (FiniteRelabelling.block squares (key v) a).length := by
    rcases a with ⟨p,a⟩
    rw [key_block,key_block]
    cases p
    · exact h a
    · exact hb a
  let e := FiniteRelabelling.of_counts squares Rendering.squares_nodup mem_squares (key u) (key v) he
  refine ⟨⟨e.forward,e.backward,e.left_inverse,e.right_inverse,?_⟩,?_⟩
  · intro s
    exact congrArg Prod.snd (e.preserves_class s)
  · intro s
    have hh : decide (v (e.forward s) = none) = decide (u s = none) := congrArg Prod.fst (e.preserves_class s)
    constructor
    · intro hv
      exact of_decide_eq_true (hh.symm.trans (by simp [hv]))
    · intro hu
      exact of_decide_eq_true (hh.trans (by simp [hu]))

theorem backward_available (u v : Board) (e : Relabelling u v) (s : Square) :
    u (e.backward s) = none ↔ v s = none := by
  have h := e.preserves_available (e.backward s)
  rw [e.right_inverse] at h
  exact h.symm

theorem transport_disjoint (u v f : Board) (e : Relabelling u v) (h : Disjoint u f) :
    Disjoint v (transport e.toRelabelling f) := by
  intro s
  rcases h (e.backward s) with hu | hf
  · exact Or.inl ((backward_available u v e s).mp hu)
  · exact Or.inr hf

theorem transport_onlyFree (u v f : Board) (e : Relabelling u v) (h : OnlyFree f) :
    OnlyFree (transport e.toRelabelling f) := fun s p hp => h (e.backward s) p hp

/-- All free canonical piece multiplicities are preserved on the actual board. -/
theorem transport_number (u v f : Board) (e : Relabelling u v) (c : Promotion.Colour) (r : Role) :
    number (transport e.toRelabelling f) c r = number f c r := by
  have hp := FiniteRelabelling.forward_perm squares Rendering.squares_nodup mem_squares e.toRelabelling
  have hm := multiplicity_transport e.toRelabelling squares f (c,r)
  have he : multiplicity (squares.map e.forward) (transport e.toRelabelling f) (c,r) =
      multiplicity squares (transport e.toRelabelling f) (c,r) := by
    exact (hp.filter _).length_eq
  rw [he] at hm
  simpa only [multiplicity,number,countWhere,Bool.and_true] using hm

end ChuShogi.ResidualSquares
