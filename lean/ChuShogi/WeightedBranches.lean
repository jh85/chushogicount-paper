import ChuShogi.MathSampling

/-! Executable interval blocks for branch ranking. Zero-weight branches have
empty fibres and receive no indices. No list of complete Boards is constructed.
Concrete file/completion branch weights must still be proved before applying
this interface to the production ranker. -/
namespace ChuShogi.WeightedBranches

abbrev Choice {n : Nat} (weights : Fin n → Nat) := Σ i, Fin (weights i)

def rank {n : Nat} (weights : Fin n → Nat) : Choice weights → Fin (∑ i, weights i) :=
  finSigmaFinEquiv

def unrank {n : Nat} (weights : Fin n → Nat) : Fin (∑ i, weights i) → Choice weights :=
  finSigmaFinEquiv.symm

theorem rank_unrank {n : Nat} (weights : Fin n → Nat) (i : Fin (∑ i, weights i)) :
    rank weights (unrank weights i) = i := finSigmaFinEquiv.apply_symm_apply i

theorem unrank_rank {n : Nat} (weights : Fin n → Nat) (x : Choice weights) :
    unrank weights (rank weights x) = x := finSigmaFinEquiv.symm_apply_apply x

/-- The rank skips precisely the preceding complete branch blocks. -/
theorem rank_offset {n : Nat} (weights : Fin n → Nat) (x : Choice weights) :
    (rank weights x).val = (∑ j : Fin x.1.val, weights (Fin.castLE x.1.isLt.le j))+x.2.val :=
  finSigmaFinEquiv_apply x

theorem uniform_input {n : Nat} (weights : Fin n → Nat)
    (p : PMF (Fin (∑ i, weights i)))
    (h : ∀ i, p i = ((∑ i, weights i : Nat) : ENNReal)⁻¹) (x : Choice weights) :
    (p.map (unrank weights)) x = ((∑ i, weights i : Nat) : ENNReal)⁻¹ :=
  MathSampling.uniform_equiv finSigmaFinEquiv.symm p _ h x

end ChuShogi.WeightedBranches
