import ChuShogi.UnrestrictedWords
import ChuShogi.WeightedBranches

/-! Independent finite canonical words and the exact multinomial branch count.
The alphabet is any finite collection of canonical roles, including emptiness.
Role occurrences are indistinguishable; no origin labels occur. -/
namespace ChuShogi.WordMultiplicity
open MultinomialPlacements
open scoped Classical

variable {a : Nat}

def Words (n : Nat) (counts : Fin a → Nat) :=
  {w : Fin n → Fin a // multiplicity w = counts}

def ways (n : Nat) (counts : Fin a → Nat) : Nat :=
  if (∑ r, counts r)=n then Nat.multinomial Finset.univ counts else 0

instance wordsFintype (n : Nat) (counts : Fin a → Nat) : Fintype (Words n counts) := by
  unfold Words
  infer_instance

theorem card_words (n : Nat) (counts : Fin a → Nat) : Fintype.card (Words n counts) = ways n counts := by
  unfold ways
  by_cases h : (∑ r, counts r)=n
  · rw [ite_eq_left h]
    have hr : ∃ f : Fin n → Fin a, multiplicity f=counts :=
      (UnrestrictedWords.realizes_iff counts).mpr (by simpa using h)
    exact profile_fiber_card ⟨counts,hr⟩
  · rw [ite_eq_right h]
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun w => h (by simpa only [← w.property,Fintype.card_fin] using sum_multiplicities w.val)⟩

def consFibre (r : Fin a) (w : Fin n → Fin a) (s : Fin a) :
    {i : Fin (n+1) // @Fin.cons n (fun _ => Fin a) r w i=s} ≃
      {_i : Fin 1 // r=s} ⊕ {i : Fin n // w i=s} where
  toFun i := Fin.cases (fun h => Sum.inl ⟨0,h⟩) (fun j h => Sum.inr ⟨j,h⟩) i.val i.property
  invFun i := match i with
    | .inl h => ⟨0,h.property⟩
    | .inr h => ⟨h.val.succ,h.property⟩
  left_inv := by
    rintro ⟨i,h⟩
    revert h
    refine Fin.cases ?_ (fun j => ?_) i
    · intro h; rfl
    · intro h; rfl
  right_inv := by
    intro i
    cases i with
    | inl h =>
      change Sum.inl (⟨0,h.property⟩ : {i : Fin 1 // r=s}) = Sum.inl h
      congr 1
      apply Subtype.ext
      exact Subsingleton.elim _ _
    | inr h => rfl

theorem multiplicity_cons (r : Fin a) (w : Fin n → Fin a) (s : Fin a) :
    multiplicity (Fin.cons r w) s = (if r=s then 1 else 0)+multiplicity w s := by
  rw [MultinomialPlacements.multiplicity,Fintype.card_congr (consFibre r w s),Fintype.card_sum]
  by_cases h : r=s <;> simp [h,MultinomialPlacements.multiplicity]

theorem multiplicity_head_tail (w : Fin (n+1) → Fin a) (s : Fin a) :
    multiplicity w s = (if w 0=s then 1 else 0)+multiplicity (fun i : Fin n => w i.succ) s := by
  have he : w=Fin.cons (w 0) (fun i => w i.succ) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  conv_lhs => rw [he]
  exact multiplicity_cons _ _ _

def decrement (counts : Fin a → Nat) (r : Fin a) : Fin a → Nat :=
  fun s => counts s - if r=s then 1 else 0

theorem tail_counts (w : Words (n+1) counts) :
    multiplicity (fun i : Fin n => w.val i.succ) = decrement counts (w.val 0) := by
  funext s
  have h := multiplicity_head_tail w.val s
  rw [congrFun w.property s] at h
  unfold decrement
  omega

theorem head_positive (w : Words (n+1) counts) : 0 < counts (w.val 0) := by
  have h := multiplicity_head_tail w.val (w.val 0)
  rw [congrFun w.property (w.val 0),ite_eq_left rfl] at h
  omega

def consEquivalence (n : Nat) (counts : Fin a → Nat) : Words (n+1) counts ≃
    Σ r : {r : Fin a // 0 < counts r}, Words n (decrement counts r.val) where
  toFun w := ⟨⟨w.val 0,head_positive w⟩,⟨fun i => w.val i.succ,tail_counts w⟩⟩
  invFun p := ⟨Fin.cons p.1.val p.2.val,by
    funext s
    rw [multiplicity_cons,congrFun p.2.property s]
    unfold decrement
    by_cases h : p.1.val=s
    · subst s
      rw [ite_eq_left rfl]
      have hp := p.1.property
      omega
    · simp [h]⟩
  left_inv := by
    intro w
    apply Subtype.ext
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv := fun _ => rfl

/-- Every possible first canonical role contributes its complete residual
multinomial count, including zero contributions from impossible tails. -/
theorem ways_succ (n : Nat) (counts : Fin a → Nat) :
    ways (n+1) counts = ∑ r : {r : Fin a // 0 < counts r}, ways n (decrement counts r.val) := by
  rw [← card_words,Fintype.card_congr (consEquivalence n counts),Fintype.card_sigma]
  simp only [card_words]

theorem ways_succ_all (n : Nat) (counts : Fin a → Nat) :
    ways (n+1) counts = ∑ r : Fin a, if 0 < counts r then ways n (decrement counts r) else 0 := by
  rw [ways_succ]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter fun r => 0 < counts r)
    (by intro r; simp) (fun r => ways n (decrement counts r))).symm

end ChuShogi.WordMultiplicity
