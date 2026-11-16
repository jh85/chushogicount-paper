import ChuShogi.WordMultiplicity
import ChuShogi.FiniteCountsArray
import ChuShogi.ArrayWords
import ChuShogi.LinearWeightedBranches

/-! Executable multinomial word ranking by complete first-role blocks. Empty
and zero-weight branches are handled explicitly. The words are independently
specified by canonical multiplicities, not by this algorithm's output. -/
namespace ChuShogi.WordIndexing
open WordMultiplicity MultinomialPlacements

variable {a : Nat}

def positiveEquivalence (n : Nat) (counts : Fin a → Nat) :
    (Σ r : Fin a, Fin (if 0 < counts r then ways n (decrement counts r) else 0)) ≃
      (Σ r : {r : Fin a // 0 < counts r}, Fin (ways n (decrement counts r.val))) where
  toFun p := by
    have hp : 0 < counts p.1 := by
      by_cases h : 0 < counts p.1
      · exact h
      · have hi := p.2.isLt; simp [h] at hi
    exact ⟨⟨p.1,hp⟩,Fin.cast (ite_eq_left hp) p.2⟩
  invFun p := ⟨p.1.val,Fin.cast (ite_eq_left p.1.property).symm p.2⟩
  left_inv := by
    rintro ⟨r,i⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Fin.ext
    simp only [Fin.val_cast]
  right_inv := by
    rintro ⟨⟨r,h⟩,i⟩
    apply Sigma.ext (Subtype.ext rfl)
    apply heq_of_eq
    apply Fin.ext
    simp only [Fin.val_cast]

def zeroEquivalence (counts : Fin a → Nat) : Fin (ways 0 counts) ≃ Words 0 counts := by
  by_cases hs : (∑ r, counts r)=0
  · have hz : ∀ r, counts r=0 := fun r => (Finset.sum_eq_zero_iff.mp hs) r (Finset.mem_univ r)
    have hw : ways 0 counts=1 := by simp [ways,Nat.multinomial,hz]
    exact {
      toFun := fun _ => ⟨Fin.elim0,by funext r; simp [MultinomialPlacements.multiplicity,hz]⟩
      invFun := fun _ => ⟨0,by rw [hw]; decide⟩
      left_inv := fun i => Fin.ext (by have hi := i.isLt; omega)
      right_inv := fun w => Subtype.ext (funext fun i => Fin.elim0 i) }
  · have hw : ways 0 counts=0 := by simp [ways,hs]
    have he (w : Words 0 counts) : False := hs (by
      rw [← w.property]
      simpa only [Fintype.card_fin] using sum_multiplicities w.val)
    exact {
      toFun := fun i => Fin.elim0 (Fin.cast hw i)
      invFun := fun w => False.elim (he w)
      left_inv := fun i => Fin.elim0 (Fin.cast hw i)
      right_inv := fun w => False.elim (he w) }

def branchEquivalence (n : Nat) (counts : Fin a → Nat)
    (tails : ∀ r : Fin a, Fin (ways n (decrement counts r)) ≃ Words n (decrement counts r)) :
    (Σ r : Fin a, Fin (if 0 < counts r then ways n (decrement counts r) else 0)) ≃ Words (n+1) counts :=
  (positiveEquivalence n counts).trans
    ((Equiv.sigmaCongrRight fun r : {r : Fin a // 0 < counts r} => tails r.val).trans
      (consEquivalence n counts).symm)

def retag (n : Nat) (u v : Fin a → Nat) (h : u=v)
    (e : Fin (ways n u) ≃ Words n u) : Fin (ways n v) ≃ Words n v := h ▸ e

def retagArray (n : Nat) (u v : Fin a → Nat) (h : u=v)
    (e : Fin (ways n u) ≃ ArrayWords.Data n u) : Fin (ways n v) ≃ ArrayWords.Data n v := h ▸ e

def arrayBranch (n : Nat) (counts : Fin a → Nat)
    (tails : ∀ r : Fin a, Fin (ways n (decrement counts r)) ≃ ArrayWords.Data n (decrement counts r)) :
    (Σ r : Fin a, Fin (if 0<counts r then ways n (decrement counts r) else 0)) ≃ ArrayWords.Data (n+1) counts :=
  (positiveEquivalence n counts).trans
    ((Equiv.sigmaCongrRight fun r : {r : Fin a // 0<counts r} => tails r.val).trans
      (ArrayWords.consEquivalence n counts).symm)

def withArray : (n : Nat) → (d : FiniteCountsArray.Data a) →
    Fin (ways n (FiniteCountsArray.read d)) ≃ ArrayWords.Data n (FiniteCountsArray.read d)
  | 0,d => (zeroEquivalence (FiniteCountsArray.read d)).trans
    (ArrayWords.equivalence 0 (FiniteCountsArray.read d)).symm
  | n+1,d => (finCongr (ways_succ_all n (FiniteCountsArray.read d))).trans
    ((LinearWeightedBranches.ofFunction _).trans
      (arrayBranch n (FiniteCountsArray.read d) (fun r =>
        retagArray n _ _ (FiniteCountsArray.read_capture (decrement (FiniteCountsArray.read d) r))
          (withArray n (FiniteCountsArray.capture (decrement (FiniteCountsArray.read d) r))))))

@[irreducible] def equivalence (n : Nat) (counts : Fin a → Nat) : Fin (ways n counts) ≃ Words n counts :=
  retag n _ _ (FiniteCountsArray.read_capture counts)
    ((withArray n (FiniteCountsArray.capture counts)).trans
      (ArrayWords.equivalence n (FiniteCountsArray.read (FiniteCountsArray.capture counts))))

def unrank (n : Nat) (counts : Fin a → Nat) := (equivalence n counts).toFun
def rank (n : Nat) (counts : Fin a → Nat) := (equivalence n counts).invFun

theorem rank_unrank (n : Nat) (counts : Fin a → Nat) (i : Fin (ways n counts)) :
    rank n counts (unrank n counts i) = i := (equivalence n counts).symm_apply_apply i

theorem unrank_rank (n : Nat) (counts : Fin a → Nat) (w : Words n counts) :
    unrank n counts (rank n counts w) = w := (equivalence n counts).apply_symm_apply w

theorem uniform_input (n : Nat) (counts : Fin a → Nat) (p : PMF (Fin (ways n counts)))
    (h : ∀ i, p i = (ways n counts : ENNReal)⁻¹) (w : Words n counts) :
    (p.map (unrank n counts)) w = (ways n counts : ENNReal)⁻¹ :=
  MathSampling.uniform_equiv (equivalence n counts) p _ h w

end ChuShogi.WordIndexing
