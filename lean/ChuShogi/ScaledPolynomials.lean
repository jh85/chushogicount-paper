import ChuShogi.RationalTable
import ChuShogi.SpecialPolynomials

/-! Integer-scaled special polynomials, constructed by complete hash-backed
convolution. Every capacity is bounded by the two original slots before the
factorial quotient is identified with its rational EGF weight. -/
namespace ChuShogi.ScaledPolynomials
open Specification Promotion ConcreteDP SummaryBridge

def lift (n : Nat) : EGFConvolution.Degree := ⟨n,0,0⟩
theorem lift_add (a b : Nat) : EGFConvolution.add (lift a) (lift b) = lift (a+b) := rfl

def typeTable (capacity : Nat) : WeightedDP.Table Nat :=
  (List.finRange (capacity+1)).map fun i => (i.val,(2 : Nat).factorial/i.val.factorial)

def product : List Nat → WeightedDP.Table Nat
  | [] => [(0,1)]
  | n::ns => HashAggregation.convolve Nat.add (typeTable n) (product ns)

def unscaled (capacities : List Nat) : EGFConvolution.Table :=
  EGFConvolution.product (capacities.map PromotedCoordinates.typeTable)

theorem type_integral (capacity : Nat) (h : capacity ≤ 2) (f : EGFConvolution.Degree → ℚ) :
    RationalTable.integral (typeTable capacity) (fun n => f (lift n)) =
      2*EGFConvolution.integral (PromotedCoordinates.typeTable capacity) f := by
  simp only [typeTable,RationalTable.integral,PromotedCoordinates.typeTable,EGFConvolution.integral,List.map_map]
  rw [EGFConvolution.mul_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  have he := PromotedEGF.special_coefficient_exact 2 capacity i.val (Nat.le_of_lt_succ i.isLt) h
  simp only [Nat.factorial_two] at he
  change (((2 : Nat)/i.val.factorial : Nat) : ℚ)*f (lift i.val) =
    2*((1/(i.val.factorial : ℚ))*f (lift i.val))
  rw [he]
  ring

/-- The complete scaled special polynomial is 2^number-of-types times the
canonical rational EGF polynomial, for every coefficient test function. -/
theorem product_integral (capacities : List Nat) (h : ∀ n ∈ capacities, n ≤ 2)
    (f : EGFConvolution.Degree → ℚ) :
    RationalTable.integral (product capacities) (fun n => f (lift n)) =
      ((2^capacities.length : Nat) : ℚ)*EGFConvolution.integral (unscaled capacities) f := by
  induction capacities generalizing f with
  | nil => simp [product,unscaled,RationalTable.integral,EGFConvolution.product,EGFConvolution.integral,lift,EGFConvolution.zero]
  | cons capacity capacities ih =>
    rw [product,RationalTable.hash_convolve,RationalTable.integral_convolve]
    have ht (i : Nat) : RationalTable.integral (product capacities) (fun n => f (lift (i+n))) =
        ((2^capacities.length : Nat) : ℚ)*EGFConvolution.integral (unscaled capacities)
          (fun d => f (EGFConvolution.add (lift i) d)) := by
      simpa only [lift_add] using ih (fun n hn => h n (by simp [hn]))
        (fun d => f (EGFConvolution.add (lift i) d))
    change RationalTable.integral (typeTable capacity)
      (fun i => RationalTable.integral (product capacities) (fun n => f (lift (i+n)))) = _
    simp_rw [ht]
    rw [RationalTable.integral_mul]
    rw [type_integral capacity (h capacity (by simp))
      (fun d => EGFConvolution.integral (unscaled capacities) (fun e => f (EGFConvolution.add d e)))]
    simp only [unscaled,List.map_cons,EGFConvolution.product,EGFConvolution.integral_convolve,
      List.length_cons,Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat]
    ring

def lance (s : Summary) : WeightedDP.Table Nat := product [s.bL,s.wL,s.bRC,s.wRC]
def goBetween (s : Summary) : WeightedDP.Table Nat := product [s.bGB,s.wGB]

theorem lance_integral (e : Summary × Nat) (he : e ∈ GroupedFiles.lanceTable)
    (f : EGFConvolution.Degree → ℚ) :
    RationalTable.integral (lance e.1) (fun n => f (lift n)) =
      16*EGFConvolution.integral (EGFConvolution.product (SpecialPolynomials.lanceTables e.1)) f := by
  have hb : ∀ n ∈ [e.1.bL,e.1.wL,e.1.bRC,e.1.wRC], n ≤ 2 := by
    intro n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact GroupCapacity.lance_cap_bound .black .lance e he
    · exact GroupCapacity.lance_cap_bound .white .lance e he
    · exact GroupCapacity.lance_cap_bound .black .chariot e he
    · exact GroupCapacity.lance_cap_bound .white .chariot e he
  exact product_integral _ hb f

theorem goBetween_integral (e : Summary × Nat) (he : e ∈ GroupedFiles.goBetweenTable)
    (f : EGFConvolution.Degree → ℚ) :
    RationalTable.integral (goBetween e.1) (fun n => f (lift n)) =
      4*EGFConvolution.integral (EGFConvolution.product (SpecialPolynomials.goBetweenTables e.1)) f := by
  have hb : ∀ n ∈ [e.1.bGB,e.1.wGB], n ≤ 2 := by
    intro n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl
    · exact GroupCapacity.goBetween_cap_bound .black .goBetween e he
    · exact GroupCapacity.goBetween_cap_bound .white .goBetween e he
  exact product_integral _ hb f

end ChuShogi.ScaledPolynomials
