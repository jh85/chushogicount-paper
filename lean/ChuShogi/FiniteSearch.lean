import Std

/-! Generic finite exploration. Every returned state has a path; a closed
returned list contains every reachable state. The closure check is a proposition
proved in Lean, not an assumed property of a worklist or external program. -/
namespace ChuShogi.FiniteSearch
variable {S : Type} [DecidableEq S]

inductive Reach (next : S → List S) (initial : S) : S → Prop
  | initial : Reach next initial initial
  | step {s t} : Reach next initial s → t ∈ next s → Reach next initial t

def explore (next : S → List S) (initial : S) : Nat → List S
  | 0 => [initial]
  | n + 1 => (explore next initial n ++ (explore next initial n).flatMap next).eraseDups

theorem explore_sound (next : S → List S) (initial : S) (n : Nat) :
    ∀ s ∈ explore next initial n, Reach next initial s := by
  induction n with
  | zero =>
    intro s hs
    have he : s = initial := by simpa [explore] using hs
    subst s
    exact Reach.initial
  | succ n ih =>
    intro s hs
    simp only [explore, List.mem_eraseDups, List.mem_append, List.mem_flatMap] at hs
    rcases hs with h | ⟨t, ht, hs⟩
    · exact ih s h
    · exact Reach.step (ih t ht) hs

omit [DecidableEq S] in
theorem closed_complete (next : S → List S) (initial : S) (states : List S)
    (hi : initial ∈ states) (hc : ∀ s ∈ states, ∀ t ∈ next s, t ∈ states) :
    ∀ s, Reach next initial s → s ∈ states := by
  intro s hs
  induction hs with
  | initial => exact hi
  | step _ ht ih => exact hc _ ih _ ht

theorem explore_exact (next : S → List S) (initial : S) (n : Nat)
    (hi : initial ∈ explore next initial n)
    (hc : ∀ s ∈ explore next initial n, ∀ t ∈ next s, t ∈ explore next initial n) (s : S) :
    s ∈ explore next initial n ↔ Reach next initial s :=
  ⟨explore_sound next initial n s, closed_complete next initial _ hi hc s⟩

end ChuShogi.FiniteSearch
