import Std

/-! Indexing a duplicate-free enumeration of an independent predicate.
This is a finite-list lemma, not the whole-Board production ranker. -/
namespace ChuShogi.Indexing
variable {A : Type} [DecidableEq A]

def unrank (xs : List A) (i : Fin xs.length) : A := xs[i.val]

def rank (xs : List A) (a : A) (h : a ∈ xs) : Fin xs.length :=
  ⟨xs.idxOf a, List.idxOf_lt_length_iff.mpr h⟩

theorem unrank_rank (xs : List A) (a : A) (h : a ∈ xs) :
    unrank xs (rank xs a h) = a := List.getElem_idxOf _

omit [DecidableEq A] in
theorem unrank_injective (xs : List A) (hn : xs.Nodup) (i j : Fin xs.length) :
    unrank xs i = unrank xs j → i = j := by
  intro h
  apply Fin.ext
  exact (List.Nodup.getElem_inj hn).mp h

theorem rank_unrank (xs : List A) (hn : xs.Nodup) (i : Fin xs.length) :
    rank xs (unrank xs i) (List.getElem_mem i.isLt) = i := by
  apply unrank_injective xs hn
  exact unrank_rank _ _ _

/-- A Fin n bijection onto precisely the independently specified objects. -/
theorem exact (xs : List A) (P : A → Prop) (hn : xs.Nodup)
    (hp : ∀ a, a ∈ xs ↔ P a) (n : Nat) (hl : xs.length = n) :
    ∃ f : Fin n → A,
      (∀ i, P (f i)) ∧
      (∀ i j, f i = f j → i = j) ∧
      (∀ a, P a → ∃ i, f i = a) := by
  subst n
  refine ⟨unrank xs, ?_, unrank_injective xs hn, ?_⟩
  · intro i; exact (hp _).mp (List.getElem_mem i.isLt)
  · intro a ha
    have hm := (hp a).mpr ha
    exact ⟨rank xs a hm, unrank_rank xs a hm⟩

end ChuShogi.Indexing
