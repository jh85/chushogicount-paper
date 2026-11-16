import ChuShogi.PolynomialSelection
import ChuShogi.HashedPolynomialFamily

/-! Executable group selection with an explicit compressed suffix polynomial.
The context is data: nested tests do not enumerate the Cartesian product of
remaining coefficient tables. The proof transports the complete family theorem.
-/
namespace ChuShogi.CompressedPolynomialSelection
open EGFConvolution CoefficientEquivalence PolynomialFamily PolynomialSelectionWeights

structure Context where
  acc : Degree
  factor : ℚ
  suffix : Table

def initial : Context := ⟨zero,1,[(zero,1)]⟩
@[noinline] def test (c : Context) (final : Degree → ℚ) (k : Degree) : ℚ :=
  c.factor*integral c.suffix (fun z => final (add c.acc (add k z)))
def prepend (c : Context) (t : Table) : Context := ⟨c.acc,c.factor,RationalCoefficientHash.convolve t c.suffix⟩
def advance (c : Context) (k : Degree) (w : ℚ) : Context := ⟨add c.acc k,c.factor*w,c.suffix⟩

theorem test_initial (final : Degree → ℚ) : test initial final=final := by
  funext k
  simp [test,initial,integral,degree_add_zero,degree_zero_add]

theorem test_prepend {B : Type} (c : Context) (y : Family B) (final : Degree → ℚ) :
    test (prepend c (HashedPolynomialFamily.table y)) final=leftTest y (test c final) := by
  funext k
  simp only [test,prepend,RationalCoefficientHash.integral_convolve,leftTest,integral_mul_test,degree_add_assoc]
  rw [HashedPolynomialFamily.equivalent y]

theorem test_advance {A : Type} (c : Context) (x : Family A) (a : A) (final : Degree → ℚ) :
    test (advance c (key x a) (weight x a)) final=rightTest x (test c final) a := by
  funext k
  simp only [test,advance,rightTest,degree_add_assoc]
  ring

def retest {A : Type} (f : Family A) (u v : Degree → ℚ) (h : u=v)
    (e : Fin (total f u) ≃ Σ a : A, Fin (score f u a)) :
    Fin (total f v) ≃ Σ a : A, Fin (score f v a) := h ▸ e

def withContext {A : Type} : (f : Family A) → (c : Context) → (final : Degree → ℚ) →
    (h : NaturalWeights f (test c final)) →
    Fin (total f (test c final)) ≃ Σ a : A, Fin (score f (test c final) a)
  | .leaf a k w,c,final,h => PolynomialSelection.leafEquivalence a k w (test c final) h
  | .product x y,c,final,h => PolynomialSelection.productEquivalence x y (test c final)
    (retest x _ _ (test_prepend c y final)
      (withContext x (prepend c (HashedPolynomialFamily.table y)) final
        ((test_prepend c y final).symm ▸ left_natural x y (test c final) h)))
    (fun a => retest y _ _ (test_advance c x a final)
      (withContext y (advance c (key x a) (weight x a)) final
        ((test_advance c x a final).symm ▸ right_natural x y (test c final) h a)))
  | .relabel f e,c,final,h => PolynomialSelection.relabelEquivalence f e (test c final)
    (withContext f c final (relabel_natural f e (test c final) h))

def equivalence {A : Type} (f : Family A) (final : Degree → ℚ) (h : NaturalWeights f final) :
    Fin (total f final) ≃ Σ a : A, Fin (score f final a) :=
  retest f _ _ (test_initial final)
    (withContext f initial final ((test_initial final).symm ▸ h))

def unrank {A : Type} (f : Family A) (final : Degree → ℚ) (h : NaturalWeights f final) := (equivalence f final h).toFun
def rank {A : Type} (f : Family A) (final : Degree → ℚ) (h : NaturalWeights f final) := (equivalence f final h).invFun

theorem rank_unrank {A : Type} (f : Family A) (final : Degree → ℚ) (h : NaturalWeights f final)
    (i : Fin (total f final)) : rank f final h (unrank f final h i)=i := (equivalence f final h).symm_apply_apply i

theorem unrank_rank {A : Type} (f : Family A) (final : Degree → ℚ) (h : NaturalWeights f final)
    (p : Σ a : A, Fin (score f final a)) : unrank f final h (rank f final h p)=p :=
  (equivalence f final h).apply_symm_apply p

end ChuShogi.CompressedPolynomialSelection
