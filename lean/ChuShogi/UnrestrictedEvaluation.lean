import ChuShogi.ReducedGeometry

/-! Source `uu` (total-count channel). This sums factorial-scaled free
coefficients using integer binomial placement factors. Restricted bishop and
kirin class contributions remain separate. -/
namespace ChuShogi.UnrestrictedEvaluation
open EGFConvolution EGFArithmetic ScaledPolynomials

def term (f0 f1 k : Nat) (d : Degree) (lab : Nat) : Nat :=
  lab * f0.descFactorial d.a0 * f1.descFactorial d.a1 *
    (k+d.m).choose d.m * (f0+f1-d.a0-d.a1).choose (k+d.m)

def fromCoefficients (cs : List (Degree × Nat)) (f0 f1 k : Nat) : Nat :=
  (cs.map fun e => term f0 f1 k e.1 e.2).sum

def uu (r : Bool) (d0 d1 k : Nat) : Nat :=
  fromCoefficients (FreeEGF.labelledCoefficients r) (72-d0) (72-d1) k

theorem term_scaling (f0 f1 k : Nat) (e : Term) (lab : Nat)
    (h : (lab : ℚ) = e.2*(e.1.m.factorial : ℚ)) :
    (k.factorial : ℚ)*(term f0 f1 k e.1 lab : ℚ) =
      e.2*CompletionCoefficients.placement f0 f1 (add e.1 (lift k)) := by
  have hs := w_terms_scaling (f0+f1-e.1.a0-e.1.a1) k e.1.m
  simp only [term,Nat.cast_mul,h,CompletionCoefficients.placement,add,lift,Nat.add_zero]
  rw [Nat.add_comm e.1.m k]
  calc
    _ = e.2*(f0.descFactorial e.1.a0 : ℚ)*(f1.descFactorial e.1.a1 : ℚ)*
        ((e.1.m.factorial : ℚ)*(k.factorial : ℚ)*((k+e.1.m).choose e.1.m : ℚ)*
          ((f0+f1-e.1.a0-e.1.a1).choose (k+e.1.m) : ℚ)) := by ring
    _ = _ := by rw [hs]; ring

theorem uu_scaling (r : Bool) (d0 d1 k : Nat) :
    (k.factorial : ℚ)*(uu r d0 d1 k : ℚ) =
      integral (FreeEGF.coefficients r) (fun d =>
        CompletionCoefficients.placement (72-d0) (72-d1) (add d (lift k))) := by
  unfold uu fromCoefficients FreeEGF.labelledCoefficients integral
  simp only [Nat.cast_list_sum,List.map_map,Function.comp_def]
  rw [mul_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  exact term_scaling _ _ _ e _ (FreeEGF.labelled_conversion r e he)

end ChuShogi.UnrestrictedEvaluation
