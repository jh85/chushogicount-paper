import ChuShogi.PromotedCoordinates

/-! The computable combined coefficient table and its complete canonical
configuration expansion. Equality of its placement evaluation with the Board
reference also requires the whole unrestricted-inventory identities. -/
namespace ChuShogi.CompletionCoefficients
open Specification Promotion ConcreteDP GroupCoverage GroupConfigurations ConfigurationFactors FiniteConfigurations
open EGFConvolution

theorem tupleWeight_append (xs ys : List Term) : tupleWeight (xs++ys) = tupleWeight xs*tupleWeight ys := by
  induction xs with
  | nil => simp [tupleWeight]
  | cons x xs ih => simp only [List.cons_append,tupleWeight,ih,mul_assoc]

theorem tupleDegree_append (xs ys : List Term) : tupleDegree (xs++ys) = add (tupleDegree xs) (tupleDegree ys) := by
  induction xs with
  | nil => simp only [List.nil_append,tupleDegree,CoefficientEquivalence.degree_zero_add]
  | cons x xs ih =>
    simp only [List.cons_append,tupleDegree,ih,CoefficientEquivalence.degree_add_assoc]

def inputs (g : Config r s) : List FreeEGF.Input :=
  FreeCoordinates.inputs (freePart g) ++ PromotedCoordinates.promotedInputs (promotedPart g)

theorem free_combine (f : Config r zero) (p : PromotedChoice s) : freePart (combine f p) = f := by
  apply config_ext <;> first | rfl | exact (free_promoted_zero f).symm

theorem promoted_combine (f : Config r zero) (p : PromotedChoice s) : promotedPart (combine f p) = p := rfl

theorem inputs_combine (f : Config r zero) (p : PromotedChoice s) : inputs (combine f p) =
    FreeCoordinates.inputs f ++ PromotedCoordinates.promotedInputs p := by
  rw [inputs,free_combine,promoted_combine]

/-- Sparse convolution of canonical free and promoted-confined coefficients. -/
def coefficients (r : Bool) (s : Summary) : Table :=
  convolve (FreeEGF.coefficients r) (PromotedCoordinates.coefficients s)

theorem coefficients_canonical (r : Bool) (s : Summary) (hs : Sized s) (f : Degree → ℚ) :
    letI := configFintype s hs r
    integral (coefficients r s) f = ∑ g : Config r s,
      tupleWeight ((inputs g).map FreeEGF.term)*f (tupleDegree ((inputs g).map FreeEGF.term)) := by
  let := configFintype s hs r
  rw [ConfigurationFactors.sum_factor r s hs]
  rw [coefficients,integral_convolve,FreeCoordinates.coefficients_canonical]
  simp_rw [PromotedCoordinates.coefficients_canonical]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro p _
  rw [inputs_combine]
  simp only [List.map_append,tupleWeight_append,tupleDegree_append,mul_assoc]

def placement (f0 f1 : Nat) (d : Degree) : ℚ :=
  (f0.descFactorial d.a0 : ℚ)*(f1.descFactorial d.a1 : ℚ)*
    ((f0+f1-d.a0-d.a1).descFactorial d.m : ℚ)

/-- Executable compressed completion evaluation. The canonical coefficient
expansion is proved above. The role-inventory refinement to the Board reference
is a separate remaining theorem, so no full counter-correctness claim is made. -/
def evaluate (r : Bool) (s : Summary) : ℚ :=
  integral (coefficients r s) (placement (72-s.d0) (72-s.d1))

end ChuShogi.CompletionCoefficients
