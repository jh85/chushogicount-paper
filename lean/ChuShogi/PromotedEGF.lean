import ChuShogi.GroupWeights

/-! Source `tok` and scaled special-type coefficients. The joint pawn limit is
kept explicit. Eligibility counts bound multiplicities; eligible origins are
not individually selected as part of a canonical Board. -/
namespace ChuShogi.PromotedEGF
open Specification Promotion ConcreteDP SummaryBridge GroupCoverage EGFArithmetic EGFConvolution

def tok (cb cw joint t : Nat) : Nat :=
  if t ≤ joint then ((List.range (t+1)).map fun b =>
    if b ≤ cb ∧ t-b ≤ cw then t.choose b else 0).sum else 0

def pawnCoefficient (cb cw joint t : Nat) : ℚ :=
  if t ≤ joint then ((List.range (t+1)).map fun b =>
    if b ≤ cb ∧ t-b ≤ cw then 1/((b.factorial : ℚ)*((t-b).factorial : ℚ)) else 0).sum else 0

theorem tok_scaling (cb cw joint t : Nat) :
    (t.factorial : ℚ)*pawnCoefficient cb cw joint t = (tok cb cw joint t : ℚ) := by
  unfold pawnCoefficient tok
  split
  · rw [mul_list_sum]
    simp only [Nat.cast_list_sum,List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro b hb
    simp only [Function.comp_def]
    have hbt : b ≤ t := by have := List.mem_range.mp hb; omega
    by_cases hc : b ≤ cb ∧ t-b ≤ cw
    · simp only [ite_eq_left hc]
      have hh := binomial_egf b (t-b)
      rw [Nat.add_sub_of_le hbt] at hh
      rw [hh]
      ring
    · simp only [ite_eq_right hc,Nat.cast_zero,mul_zero]
  · simp

def specialCoefficients (stock capacity : Nat) : List Nat :=
  (List.range (capacity+1)).map fun i => stock.factorial/i.factorial

theorem special_coefficient_exact (stock capacity i : Nat)
    (hi : i ≤ capacity) (hc : capacity ≤ stock) :
    ((stock.factorial/i.factorial : Nat) : ℚ) =
      (stock.factorial : ℚ)*(1/(i.factorial : ℚ)) := by
  rw [factorial_ratio i stock (hi.trans hc)]
  ring

/-- The actual six non-pawn type capacities satisfy the exact-scaling premise
on every summary occurring in the default compact DP. -/
theorem realized_special_exact (s : Summary) (hs : CompactSummary.RealizedCompact s)
    (c : Colour) (k : Kind) (hk : k ≠ .pawn) (i : Nat) (hi : i ≤ cap s c k) :
    ((((2 : Nat).factorial)/i.factorial : Nat) : ℚ) =
      ((2 : Nat).factorial : ℚ)*(1/(i.factorial : ℚ)) :=
  special_coefficient_exact 2 (cap s c k) i hi ((sized_compact_realized s hs).2.1 c k hk)

/-- The source's factorial(k)//factorial(t) factor is exact for k=t+r. -/
theorem vector_term (t r tv cv : Nat) :
    ((tv*cv*((t+r).factorial/t.factorial) : Nat) : ℚ) =
      ((tv : ℚ)/(t.factorial : ℚ))*(cv : ℚ)*((t+r).factorial : ℚ) := by
  rw [Nat.cast_mul,Nat.cast_mul,factorial_ratio t (t+r) (by omega)]
  ring

end ChuShogi.PromotedEGF
