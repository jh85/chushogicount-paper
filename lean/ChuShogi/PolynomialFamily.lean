import ChuShogi.FiniteCoefficientModel
import ChuShogi.FiniteListEquivalence

/-! Explicit finite canonical-choice products with executable coefficient
tables. Fintype adapters below are for symbolic proofs; table evaluation never
enumerates a product of choices. Equal coefficient terms retain every labelled
canonical choice contribution, without assuming term-image injectivity. -/
namespace ChuShogi.PolynomialFamily
open EGFConvolution

structure Alphabet (A : Type) where
  decEq : DecidableEq A
  values : List A
  nodup : values.Nodup
  complete : ∀ a, a ∈ values

inductive Family : Type → Type 1 where
  | leaf {A : Type} (alphabet : Alphabet A) (key : A → Degree) (weight : A → ℚ) : Family A
  | product {A B : Type} : Family A → Family B → Family (A × B)
  | relabel {A B : Type} : Family A → (A ≃ B) → Family B

def key {A : Type} : Family A → A → Degree
  | .leaf _ key _,a => key a
  | .product x y,a => add (key x a.1) (key y a.2)
  | .relabel x e,a => key x (e.symm a)

def weight {A : Type} : Family A → A → ℚ
  | .leaf _ _ weight,a => weight a
  | .product x y,a => weight x a.1*weight y a.2
  | .relabel x e,a => weight x (e.symm a)

def table {A : Type} : Family A → Table
  | .leaf a key weight => a.values.map fun x => (key x,weight x)
  | .product x y => convolve (table x) (table y)
  | .relabel x _ => table x

@[instance_reducible] noncomputable def fintype {A : Type} : Family A → Fintype A
  | .leaf a _ _ => by
    let := a.decEq
    exact Fintype.ofList a.values a.complete
  | .product x y => by
    letI := fintype x
    letI := fintype y
    infer_instance
  | .relabel x e => by
    letI := fintype x
    exact Fintype.ofEquiv _ e

/-- Complete coefficient semantics, including all choices whose images merge
at a sparse polynomial key. There is no externally supplied coverage premise. -/
theorem table_spec {A : Type} (f : Family A) (test : Degree → ℚ) :
    letI := fintype f
    integral (table f) test = ∑ a, weight f a*test (key f a) := by
  induction f generalizing test with
  | leaf a k w =>
    let := a.decEq
    let := fintype (Family.leaf a k w)
    exact (FiniteCoefficientModel.fromList a.values a.nodup a.complete k w).correct test
  | @product A B x y ix iy =>
    let := fintype x
    let := fintype y
    rw [table,integral_convolve,ix]
    simp_rw [iy]
    rw [Fintype.sum_prod_type]
    simp only [weight,key,Finset.mul_sum,mul_assoc]
  | @relabel A B x e ix =>
    let := fintype x
    let := fintype (Family.relabel x e)
    rw [table,ix]
    exact Fintype.sum_equiv e _ _ (fun a => by simp only [weight,key,Equiv.symm_apply_apply])

def members {A : Type} [DecidableEq A] (xs : List A) (hn : xs.Nodup)
    (key : A → Degree) (weight : A → ℚ) : Family {a : A // a ∈ xs} :=
  .leaf ⟨inferInstance,xs.attach,hn.attach,fun a => by simp⟩
    (fun a => key a.val) (fun a => weight a.val)

def unit : Family Unit := .leaf ⟨inferInstance,[()],by simp,by intro a; cases a; simp⟩ (fun _ => zero) (fun _ => 1)

def power {A : Type} (f : Family A) : (n : Nat) → Family (Fin n → A)
  | 0 => .relabel unit (FiniteCoefficientModel.emptyFunction A)
  | n+1 => .relabel (.product f (power f n)) (FiniteCoefficientModel.functionSplit A n).symm

end ChuShogi.PolynomialFamily
