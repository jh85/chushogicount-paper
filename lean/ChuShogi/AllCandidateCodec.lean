import ChuShogi.EfficientBoardCodec
import ChuShogi.CandidatePartition

/-! Disjoint royal-stratum intervals index all independent I1--I9 candidates.
The input law is a mathematical uniform-integer law, not a claim about an RNG. -/
namespace ChuShogi.AllCandidateCodec
open Specification

instance royalDecidable (b : Board) : Decidable (hasRoyal b .black) :=
  inferInstanceAs (Decidable (0<number b .black (.native .king)))

def partition : {b : Board // C_r b} ⊕ {b : Board // C_nr b} ≃ {b : Board // Candidate b} where
  toFun x := match x with
    | .inl b => ⟨b.val,b.property.1⟩
    | .inr b => ⟨b.val,b.property.1⟩
  invFun b := if h : hasRoyal b.val .black then .inl ⟨b.val,b.property,h⟩ else .inr ⟨b.val,b.property,h⟩
  left_inv x := by cases x with
    | inl b => simp only [dite_eq_left b.property.2]
    | inr b => simp only [dite_eq_right b.property.2]
  right_inv b := by
    dsimp only
    by_cases h : hasRoyal b.val .black
    · rw [dite_eq_left h]
    · rw [dite_eq_right h]

def count : Nat := CachedArithmetic.count true+CachedArithmetic.count false

theorem count_correct : count=FiniteBoards.card Candidate := by
  rw [count,CachedArithmetic.count_C_r,CachedArithmetic.count_C_nr,CandidatePartition.card_split]

@[irreducible] def equivalence (r : EfficientBoardCodec.Runtime true) (nr : EfficientBoardCodec.Runtime false) :
    Fin count ≃ {b : Board // Candidate b} :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr r.codec nr.codec).trans partition)

def unrank (r : EfficientBoardCodec.Runtime true) (nr : EfficientBoardCodec.Runtime false) := (equivalence r nr).toFun
def rank (r : EfficientBoardCodec.Runtime true) (nr : EfficientBoardCodec.Runtime false) := (equivalence r nr).invFun

theorem rank_unrank (r : EfficientBoardCodec.Runtime true) (nr : EfficientBoardCodec.Runtime false) (i : Fin count) :
    rank r nr (unrank r nr i)=i := (equivalence r nr).symm_apply_apply i

theorem unrank_rank (r : EfficientBoardCodec.Runtime true) (nr : EfficientBoardCodec.Runtime false) (b : {b : Board // Candidate b}) :
    unrank r nr (rank r nr b)=b := (equivalence r nr).apply_symm_apply b

theorem uniform_input (r : EfficientBoardCodec.Runtime true) (nr : EfficientBoardCodec.Runtime false)
    (p : PMF (Fin count)) (h : ∀ i, p i=(count : ENNReal)⁻¹) (b : {b : Board // Candidate b}) :
    (p.map (unrank r nr)) b=(count : ENNReal)⁻¹ := MathSampling.uniform_equiv (equivalence r nr) p _ h b

end ChuShogi.AllCandidateCodec
