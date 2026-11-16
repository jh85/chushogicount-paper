import ChuShogi.PolynomialSelectionWeights
import ChuShogi.LinearWeightedBranches

/-! Executable rank/unrank of complete canonical-choice products by compressed
coefficient suffixes. Naturalness is required only of complete contributions;
the proof derives exact natural weights for every intermediate branch.
-/
namespace ChuShogi.PolynomialSelection
open EGFConvolution PolynomialFamily PolynomialSelectionWeights

theorem sum_get (xs : List A) (f : A → Nat) :
    (xs.map f).sum = ∑ i : Fin xs.length, f xs[i.val] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simpa only [List.map_cons,List.sum_cons,List.length_cons,Fin.sum_univ_succ,
      List.getElem_cons_zero,List.getElem_cons_succ,Fin.val_zero,Fin.val_succ] using
      congrArg (fun n => f x+n) ih

theorem leaf_total {A : Type} (a : Alphabet A) (k : A → Degree) (w : A → ℚ)
    (test : Degree → ℚ) (h : NaturalWeights (.leaf a k w) test) :
    total (.leaf a k w) test=(a.values.map (score (.leaf a k w) test)).sum := by
  let := a.decEq
  let := fintype (Family.leaf a k w)
  rw [total_eq_sum _ _ h]
  have he : a.values.toFinset=Finset.univ := Finset.ext (fun x => by simp [a.complete x])
  rw [← he,List.sum_toFinset _ a.nodup]

def leafEquivalence {A : Type} (a : Alphabet A) (k : A → Degree) (w : A → ℚ)
    (test : Degree → ℚ) (h : NaturalWeights (.leaf a k w) test) :
    Fin (total (.leaf a k w) test) ≃ Σ x : A, Fin (score (.leaf a k w) test x) := by
  letI := a.decEq
  exact (finCongr (leaf_total a k w test h)).trans
    ((LinearWeightedBranches.onList a.values _).trans
      (Equiv.sigmaCongrLeft (β := fun x : A => Fin (score (.leaf a k w) test x))
        (FiniteListEquivalence.equivalence a.values a.nodup a.complete)))

def flatten {A B : Type} (f : A × B → Nat) :
    (Σ a : A, Σ b : B, Fin (f (a,b))) ≃ Σ p : A × B, Fin (f p) where
  toFun p := ⟨(p.1,p.2.1),p.2.2⟩
  invFun p := ⟨p.1.1,p.1.2,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def productEquivalence {A B : Type} (x : Family A) (y : Family B) (test : Degree → ℚ)
    (left : Fin (total x (leftTest y test)) ≃ Σ a : A, Fin (score x (leftTest y test) a))
    (right : ∀ a : A, Fin (total y (rightTest x test a)) ≃ Σ b : B, Fin (score y (rightTest x test a) b)) :
    Fin (total (.product x y) test) ≃ Σ p : A × B, Fin (score (.product x y) test p) :=
  (finCongr (product_total x y test)).trans
    (left.trans ((Equiv.sigmaCongrRight fun a : A =>
      (finCongr (left_score_right_total x y test a)).trans
        ((right a).trans (Equiv.sigmaCongrRight fun b : B => finCongr (right_score_product x y test a b)))).trans
      (flatten (score (.product x y) test))))

def relabelEquivalence {A B : Type} (f : Family A) (e : A ≃ B) (test : Degree → ℚ)
    (child : Fin (total f test) ≃ Σ a : A, Fin (score f test a)) :
    Fin (total (.relabel f e) test) ≃ Σ b : B, Fin (score (.relabel f e) test b) :=
  child.trans ((Equiv.sigmaCongrRight fun a : A => finCongr (relabel_score f e test a)).trans
    (Equiv.sigmaCongrLeft (β := fun b : B => Fin (score (.relabel f e) test b)) e))

def equivalence {A : Type} : (f : Family A) → (test : Degree → ℚ) → (h : NaturalWeights f test) →
    Fin (total f test) ≃ Σ a : A, Fin (score f test a)
  | .leaf a k w,test,h => leafEquivalence a k w test h
  | .product x y,test,h => productEquivalence x y test
    (equivalence x (leftTest y test) (left_natural x y test h))
    (fun a => equivalence y (rightTest x test a) (right_natural x y test h a))
  | .relabel f e,test,h => relabelEquivalence f e test
    (equivalence f test (relabel_natural f e test h))

def unrank {A : Type} (f : Family A) (test : Degree → ℚ) (h : NaturalWeights f test) := (equivalence f test h).toFun
def rank {A : Type} (f : Family A) (test : Degree → ℚ) (h : NaturalWeights f test) := (equivalence f test h).invFun

theorem rank_unrank {A : Type} (f : Family A) (test : Degree → ℚ) (h : NaturalWeights f test)
    (i : Fin (total f test)) : rank f test h (unrank f test h i)=i := (equivalence f test h).symm_apply_apply i

theorem unrank_rank {A : Type} (f : Family A) (test : Degree → ℚ) (h : NaturalWeights f test)
    (x : Σ a : A, Fin (score f test a)) : unrank f test h (rank f test h x)=x :=
  (equivalence f test h).apply_symm_apply x

theorem uniform_input {A : Type} (f : Family A) (test : Degree → ℚ) (h : NaturalWeights f test)
    (p : PMF (Fin (total f test))) (hp : ∀ i, p i=(total f test : ENNReal)⁻¹)
    (x : Σ a : A, Fin (score f test a)) : (p.map (unrank f test h)) x=(total f test : ENNReal)⁻¹ :=
  MathSampling.uniform_equiv (equivalence f test h) p _ hp x

end ChuShogi.PolynomialSelection
