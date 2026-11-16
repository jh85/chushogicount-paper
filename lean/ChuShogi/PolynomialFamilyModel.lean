import ChuShogi.PolynomialFamily

/-! Reuse the checked canonical coefficient models to identify an executable
choice-family tree's table, key and weight. Equality of individual term images
is not an injectivity assumption. -/
namespace ChuShogi.PolynomialFamilyModel
open PolynomialFamily EGFConvolution

structure Matches {A : Type} [Fintype A] (f : Family A) (m : FiniteCoefficientModel.Model A) : Prop where
  table : PolynomialFamily.table f=m.table
  key : ∀ a, PolynomialFamily.key f a=m.key a
  weight : ∀ a, PolynomialFamily.weight f a=m.weight a

theorem product {A B : Type} [Fintype A] [Fintype B] {f : Family A} {g : Family B}
    {m : FiniteCoefficientModel.Model A} {n : FiniteCoefficientModel.Model B}
    (hf : Matches f m) (hg : Matches g n) : Matches (.product f g) (FiniteCoefficientModel.product m n) := by
  constructor
  · exact congrArg₂ convolve hf.table hg.table
  · intro a
    change add (key f a.1) (key g a.2)=add (m.key a.1) (n.key a.2)
    rw [hf.key,hg.key]
  · intro a
    change weight f a.1*weight g a.2=m.weight a.1*n.weight a.2
    rw [hf.weight,hg.weight]

theorem relabel {A B : Type} [Fintype A] [Fintype B] {f : Family A}
    {m : FiniteCoefficientModel.Model A} (h : Matches f m) (e : A ≃ B) :
    Matches (.relabel f e) (FiniteCoefficientModel.relabel m e) := by
  constructor
  · exact h.table
  · intro b; exact h.key (e.symm b)
  · intro b; exact h.weight (e.symm b)

theorem unit : Matches PolynomialFamily.unit FiniteCoefficientModel.unit :=
  ⟨rfl,fun _ => rfl,fun _ => rfl⟩

theorem power {A : Type} [Fintype A] {f : Family A} {m : FiniteCoefficientModel.Model A}
    (h : Matches f m) (n : Nat) : Matches (PolynomialFamily.power f n) (FiniteCoefficientModel.power m n) := by
  induction n with
  | zero => exact relabel unit (FiniteCoefficientModel.emptyFunction A)
  | succ n ih => exact relabel (product h ih) (FiniteCoefficientModel.functionSplit A n).symm

theorem members {A : Type} [DecidableEq A] (xs : List A) (hn : xs.Nodup)
    (key : A → Degree) (weight : A → ℚ) :
    Matches (PolynomialFamily.members xs hn key weight) (FiniteCoefficientModel.members xs hn key weight) :=
  ⟨rfl,fun _ => rfl,fun _ => rfl⟩

end ChuShogi.PolynomialFamilyModel
