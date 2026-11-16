import ChuShogi.PromotedCoefficientSupport
import ChuShogi.CachedArithmetic

/-! Individual completion weights using labelled promoted coefficients and
shared integer uu values. Unlike the four-field total reduction, this evaluator
retains exactly the summary needed by a file branch or a Board codec. -/
namespace ChuShogi.CompletionArithmetic
open ConcreteDP EGFConvolution PromotedCoefficientSupport

def withU (u : List Nat → Nat) (s : Summary) : Nat :=
  ((labelled s).map fun e => e.2*u [s.d0,s.d1,e.1]).sum

def uReference (r : Bool) (xs : List Nat) : Nat :=
  UnrestrictedEvaluation.uu r (xs[0]?.getD 0) (xs[1]?.getD 0) (xs[2]?.getD 0)
def evaluate (r : Bool) (s : Summary) : Nat := withU (uReference r) s

theorem evaluate_cast (r : Bool) (s : Summary) : (evaluate r s : ℚ)=CompletionCoefficients.evaluate r s := by
  unfold evaluate withU labelled
  simp only [Nat.cast_list_sum,List.map_map,Function.comp_def,Nat.cast_mul,uReference,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
  rw [CompletionCoefficients.evaluate,CompletionCoefficients.coefficients,
    CoefficientEquivalence.convolve_comm _ _ (CompletionCoefficients.placement (72-s.d0) (72-s.d1)),integral_convolve]
  unfold integral
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  rw [labelled_conversion s e he]
  have hs := coefficients_lift s e he
  have hu := UnrestrictedEvaluation.uu_scaling r s.d0 s.d1 e.1.m
  change e.2*(e.1.m.factorial : ℚ)*(UnrestrictedEvaluation.uu r s.d0 s.d1 e.1.m : ℚ) =
    e.2*EGFConvolution.integral (FreeEGF.coefficients r)
      (fun k => CompletionCoefficients.placement (72-s.d0) (72-s.d1) (add e.1 k))
  rw [mul_assoc,hu]
  apply congrArg (e.2*·)
  apply congrArg (EGFConvolution.integral (FreeEGF.coefficients r))
  funext k
  rw [hs,CoefficientEquivalence.degree_add_comm]
  rfl

theorem evaluate_correct (r : Bool) (s : Summary) : evaluate r s=EvaluatorRefinement.evaluateNat r s := by
  unfold EvaluatorRefinement.evaluateNat
  rw [← evaluate_cast]
  simp

@[noinline] def fromCoefficients (cs : List (Degree × Nat)) (s : Summary) : Nat :=
  withU (CachedArithmetic.fromCoefficients cs) s

theorem fromCoefficients_correct (r : Bool) (s : Summary) :
    fromCoefficients (FreeEGF.labelledCoefficients r) s=EvaluatorRefinement.evaluateNat r s := by
  rw [← evaluate_correct]
  apply congrArg (fun u => withU u s)
  exact CachedArithmetic.unrestricted_correct r

end ChuShogi.CompletionArithmetic
