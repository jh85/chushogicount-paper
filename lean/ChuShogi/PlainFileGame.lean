import ChuShogi.FiniteSearch
import ChuShogi.PlainFile

/-!
The ordinary abstract file game: 0=captured, 13=promoted, 1--12=present rank.
Moves are capture, an unobstructed pawn step, or promotion on such a step when
its origin or destination is in the zone. This is a Lean reference transition
system, not a formal semantics of the original Python interpreter.
-/
namespace ChuShogi.PlainFileGame
open FiniteSearch

abbrev State := Fin 14 × Fin 14

def present (r : Fin 14) : Bool := 0 < r.val && r.val ≤ 12

def next (s : State) : List State := Id.run do
  let (b, w) := s
  let mut out := []
  if present b then
    out := (⟨0, by omega⟩, w) :: out
    if h : b.val + 1 ≤ 12 ∧ b.val + 1 ≠ w.val then
      out := (⟨b.val + 1, by omega⟩, w) :: out
      if 9 ≤ b.val + 1 then
        out := (⟨13, by omega⟩, w) :: out
  if present w then
    out := (b, ⟨0, by omega⟩) :: out
    if h : 1 ≤ w.val - 1 ∧ w.val - 1 ≠ b.val then
      out := (b, ⟨w.val - 1, by omega⟩) :: out
      if w.val - 1 ≤ 4 then
        out := (b, ⟨13, by omega⟩) :: out
  return out

def initial : State := (⟨4, by omega⟩, ⟨9, by omega⟩)

def projectRank (r : Fin 14) : Option PlainFile.Rank :=
  if h : 1 ≤ r.val ∧ r.val ≤ 12 then some ⟨r.val - 1, by omega⟩ else none

def project (s : State) : PlainFile.Config := (projectRank s.1, projectRank s.2)

/-- Independent local constraints, including the joint promotion restriction. -/
def Classified (s : State) : Prop :=
  PlainFile.Admissible (project s) ∧
  (s.1.val = 13 → s.2.val = 0) ∧ (s.2.val = 13 → s.1.val = 0)

instance (s : State) : Decidable (Classified s) :=
  inferInstanceAs (Decidable (PlainFile.Admissible (project s) ∧
    (s.1.val = 13 → s.2.val = 0) ∧ (s.2.val = 13 → s.1.val = 0)))

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Small finite closure checks use ordinary kernel reduction. -/
theorem classified_initial : Classified initial := by decide

theorem classified_closed (s : State) (h : Classified s) (t : State) (ht : t ∈ next s) :
    Classified t := by
  have checked : ∀ b w : Fin 14, Classified (b,w) →
      (next (b,w)).all (fun t => decide (Classified t)) = true := by decide
  have ha := (List.all_eq_true.mp (checked s.1 s.2 h)) t ht
  exact of_decide_eq_true ha

theorem classified_reached (s : State) (h : Classified s) : s ∈ explore next initial 9 := by
  have checked : ∀ b w : Fin 14, Classified (b,w) → (b,w) ∈ explore next initial 9 := by decide
  exact checked s.1 s.2 h

/-- Soundness and completeness against the independent predicate. -/
theorem reach_iff (s : State) : Reach next initial s ↔ Classified s := by
  constructor
  · intro hs
    induction hs with
    | initial => exact classified_initial
    | step _ ht ih => exact classified_closed _ ih _ ht
  · intro hs
    exact explore_sound _ _ _ s (classified_reached s hs)

def states : List State :=
  ((List.finRange 14).flatMap fun b => (List.finRange 14).map fun w => (b,w)).filter
    fun s => decide (Classified s)

theorem states_length : states.length = 36 := by decide

theorem states_iff (s : State) : s ∈ states ↔ Reach next initial s := by
  rw [reach_iff]
  rcases s with ⟨b,w⟩
  simp [states]

theorem states_nodup : states.Nodup := by decide

end ChuShogi.PlainFileGame
