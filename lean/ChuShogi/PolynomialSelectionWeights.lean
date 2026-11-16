import ChuShogi.PolynomialFamily
import ChuShogi.CoefficientEquivalence

/-! Exact natural branch weights from a rational coefficient family. Only
complete terminal contributions must be natural; individual EGF coefficients
and intermediate products need not be integers. -/
namespace ChuShogi.PolynomialSelectionWeights
open EGFConvolution PolynomialFamily

def NaturalWeights {A : Type} (f : Family A) (test : Degree → ℚ) : Prop :=
  ∀ a, ∃ n : Nat, weight f a*test (key f a)=(n : ℚ)
def score {A : Type} (f : Family A) (test : Degree → ℚ) (a : A) : Nat :=
  (weight f a*test (key f a)).num.toNat
def total {A : Type} (f : Family A) (test : Degree → ℚ) : Nat := (integral (table f) test).num.toNat

theorem score_cast {A : Type} (f : Family A) (test : Degree → ℚ) (h : NaturalWeights f test) (a : A) :
    (score f test a : ℚ)=weight f a*test (key f a) := by
  obtain ⟨n,hn⟩ := h a
  simp only [score,hn]
  simp

theorem integral_scores {A : Type} (f : Family A) (test : Degree → ℚ) (h : NaturalWeights f test) :
    letI := fintype f
    integral (table f) test = ((∑ a, score f test a : Nat) : ℚ) := by
  let := fintype f
  rw [table_spec,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact (score_cast f test h a).symm

theorem total_eq_sum {A : Type} (f : Family A) (test : Degree → ℚ) (h : NaturalWeights f test) :
    letI := fintype f
    total f test=∑ a, score f test a := by
  let := fintype f
  unfold total
  rw [integral_scores f test h]
  generalize (∑ a, score f test a : Nat)=n
  simp

theorem total_cast {A : Type} (f : Family A) (test : Degree → ℚ) (h : NaturalWeights f test) :
    (total f test : ℚ)=integral (table f) test := by
  let := fintype f
  rw [total_eq_sum f test h,integral_scores f test h]

def leftTest {B : Type} (y : Family B) (test : Degree → ℚ) (ka : Degree) : ℚ :=
  integral (table y) (fun kb => test (add ka kb))
def rightTest {A : Type} (x : Family A) (test : Degree → ℚ) (a : A) (kb : Degree) : ℚ :=
  weight x a*test (add (key x a) kb)

theorem left_natural {A B : Type} (x : Family A) (y : Family B) (test : Degree → ℚ)
    (h : NaturalWeights (.product x y) test) : NaturalWeights x (leftTest y test) := by
  intro a
  let := fintype y
  refine ⟨∑ b, score (.product x y) test (a,b),?_⟩
  rw [leftTest,table_spec,Finset.mul_sum,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro b _
  simpa only [weight,key,mul_assoc] using (score_cast (.product x y) test h (a,b)).symm

theorem right_natural {A B : Type} (x : Family A) (y : Family B) (test : Degree → ℚ)
    (h : NaturalWeights (.product x y) test) (a : A) : NaturalWeights y (rightTest x test a) := by
  intro b
  obtain ⟨n,hn⟩ := h (a,b)
  refine ⟨n,?_⟩
  rw [← hn]
  change weight y b*(weight x a*test (add (key x a) (key y b))) =
    (weight x a*weight y b)*test (add (key x a) (key y b))
  ring

theorem product_total {A B : Type} (x : Family A) (y : Family B) (test : Degree → ℚ) :
    total (.product x y) test=total x (leftTest y test) := by
  unfold total
  rw [table,integral_convolve]
  rfl

theorem left_score_right_total {A B : Type} (x : Family A) (y : Family B) (test : Degree → ℚ) (a : A) :
    score x (leftTest y test) a=total y (rightTest x test a) := by
  unfold score total rightTest leftTest
  rw [CoefficientEquivalence.integral_mul_test]

theorem right_score_product {A B : Type} (x : Family A) (y : Family B) (test : Degree → ℚ) (a : A) (b : B) :
    score y (rightTest x test a) b=score (.product x y) test (a,b) := by
  unfold score
  apply congrArg (fun q : ℚ => q.num.toNat)
  change weight y b*(weight x a*test (add (key x a) (key y b))) =
    (weight x a*weight y b)*test (add (key x a) (key y b))
  ring

theorem relabel_natural {A B : Type} (f : Family A) (e : A ≃ B) (test : Degree → ℚ)
    (h : NaturalWeights (.relabel f e) test) : NaturalWeights f test := by
  intro a
  simpa only [weight,key,Equiv.symm_apply_apply] using h (e a)

theorem relabel_score {A B : Type} (f : Family A) (e : A ≃ B) (test : Degree → ℚ) (a : A) :
    score f test a=score (.relabel f e) test (e a) := by
  simp only [score,weight,key,Equiv.symm_apply_apply]

end ChuShogi.PolynomialSelectionWeights
