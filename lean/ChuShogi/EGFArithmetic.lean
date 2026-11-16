module
public import ChuShogi.MultinomialPlacements
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Rational EGF arithmetic. Intermediate coefficients need not be integral.
The factorial-scaled coefficient, not the coefficient itself, counts labelled
words of canonical roles. Integer division is used only with a proved divisor. -/
namespace ChuShogi.EGFArithmetic
open scoped BigOperators

theorem cast_exact_div (a b : Nat) (hb : b ≠ 0) (h : b ∣ a) :
    ((a / b : Nat) : ℚ) = (a : ℚ) / (b : ℚ) := by
  apply (eq_div_iff (by exact_mod_cast hb)).mpr
  exact_mod_cast Nat.div_mul_cancel h

theorem factorial_ratio (a b : Nat) (h : a ≤ b) :
    ((b.factorial / a.factorial : Nat) : ℚ) = (b.factorial : ℚ) / (a.factorial : ℚ) :=
  cast_exact_div _ _ (Nat.factorial_ne_zero _) (Nat.factorial_dvd_factorial h)

variable {R : Type} [Fintype R]

def inverseFactorials (n : R → Nat) : ℚ := ∏ r, (1 / ((n r).factorial : ℚ))

/-- The exact EGF scaling identity, for arbitrary canonical multiplicities. -/
theorem factorial_scaling (n : R → Nat) :
    (((∑ r, n r).factorial : Nat) : ℚ) * inverseFactorials n =
      (Nat.multinomial Finset.univ n : ℚ) := by
  classical
  have hn : (∏ r, (n r).factorial) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun _ _ => Nat.factorial_ne_zero _)
  rw [Nat.multinomial,cast_exact_div _ _ hn (Nat.prod_factorial_dvd_factorial_sum _ _)]
  simp [inverseFactorials,div_eq_mul_inv,Finset.prod_inv_distrib]

/-- Choosing occupied squares and assigning the canonical roles gives the
falling-factorial EGF evaluation, including the zero case when overfull. -/
theorem placement_scaling (f : Nat) (n : R → Nat) :
    ((f.choose (∑ r, n r) * Nat.multinomial Finset.univ n : Nat) : ℚ) =
      (f.descFactorial (∑ r, n r) : ℚ) * inverseFactorials n := by
  rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul,Nat.cast_mul]
  rw [mul_right_comm, factorial_scaling]
  exact mul_comm _ _

/-- The binomial factors in source `w_terms` merge the two unrestricted word
lengths exactly. There is no divisibility assumption on the EGF coefficient. -/
theorem w_terms_scaling (f k j : Nat) :
    (j.factorial : ℚ) * (k.factorial : ℚ) * ((k+j).choose j : ℚ) *
      (f.choose (k+j) : ℚ) = (f.descFactorial (k+j) : ℚ) := by
  have h : (k+j).choose j * j.factorial * k.factorial = (k+j).factorial := by
    simpa only [Nat.add_sub_cancel_right] using
      (Nat.choose_mul_factorial_mul_factorial (n := k+j) (k := j) (by omega))
  have hc : ((k+j).choose j : ℚ) * (j.factorial : ℚ) * (k.factorial : ℚ) =
      ((k+j).factorial : ℚ) := by exact_mod_cast h
  rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul,← hc]
  ring

theorem binomial_egf (b w : Nat) :
    ((b+w).choose b : ℚ) = ((b+w).factorial : ℚ) /
      ((b.factorial : ℚ)*(w.factorial : ℚ)) := by
  apply (eq_div_iff (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero b)
    (by exact_mod_cast Nat.factorial_ne_zero w))).mpr
  have h : (b+w).choose b*b.factorial*w.factorial = (b+w).factorial := by
    simpa only [Nat.add_sub_cancel_left] using
      (Nat.choose_mul_factorial_mul_factorial (n := b+w) (k := b) (by omega))
  rw [← mul_assoc]
  exact_mod_cast h

/-- A natural-number final numerator with a proved cardinality identity admits
exact integer scaling division. This lemma does not supply that identity. -/
theorem final_division (numerator scale count : Nat) (hs : scale ≠ 0)
    (h : (numerator : ℚ) = (scale : ℚ)*(count : ℚ)) :
    scale ∣ numerator ∧ numerator/scale = count := by
  have he : numerator = scale*count := by exact_mod_cast h
  subst numerator
  exact ⟨Nat.dvd_mul_right _ _,Nat.mul_div_cancel_left count (Nat.pos_of_ne_zero hs)⟩

theorem falling_remainders (f0 f1 a0 a1 m : Nat) :
    f0.descFactorial a0*f1.descFactorial a1*((f0-a0)+(f1-a1)).descFactorial m =
      f0.descFactorial a0*f1.descFactorial a1*(f0+f1-a0-a1).descFactorial m := by
  by_cases h0 : a0 ≤ f0
  · by_cases h1 : a1 ≤ f1
    · rw [show (f0-a0)+(f1-a1) = f0+f1-a0-a1 by omega]
    · have hz : f1.descFactorial a1 = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [hz]; simp
  · have hz : f0.descFactorial a0 = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [hz]; simp

theorem rational_falling_remainders (f0 f1 a0 a1 m : Nat) :
    (f0.descFactorial a0 : ℚ)*(f1.descFactorial a1 : ℚ)*(((f0-a0)+(f1-a1)).descFactorial m : ℚ) =
      (f0.descFactorial a0 : ℚ)*(f1.descFactorial a1 : ℚ)*((f0+f1-a0-a1).descFactorial m : ℚ) := by
  exact_mod_cast falling_remainders f0 f1 a0 a1 m

theorem bound_selections (A S : Type) [Fintype A] [Fintype S] :
    Fintype.card (A ↪ S) = (Fintype.card S).descFactorial (Fintype.card A) :=
  Fintype.card_embedding_eq

end ChuShogi.EGFArithmetic
