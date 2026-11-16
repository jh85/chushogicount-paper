import ChuShogi.SummarySufficiency

/-! Concrete, purely arithmetic completion profile predicates, independently of
any group-state or polynomial enumeration. -/
namespace ChuShogi.CompletionProfiles
open Specification Promotion ConcreteDP BoardDecomposition SummaryBridge Completion SummarySufficiency

abbrev Counts := Colour → Role → Nat

def profile (b : Board) (a : Nat) : Counts := fun c r =>
  countWhere b c r (fun s => decide (squareClass s = a))

def total (n0 n1 : Counts) : Counts := fun c r => n0 c r + n1 c r

theorem number_profile (b : Board) (c : Colour) (r : Role) :
    number b c r = total (profile b 0) (profile b 1) c r := by
  have hi (xs : List Square) :
      (xs.filter fun s => decide (b s = some (c,r))).length =
      (xs.filter fun s => decide (b s = some (c,r)) && decide (squareClass s = 0)).length +
      (xs.filter fun s => decide (b s = some (c,r)) && decide (squareClass s = 1)).length := by
    induction xs with
    | nil => rfl
    | cons s xs ih =>
      have ha : squareClass s = 0 ∨ squareClass s = 1 := by unfold squareClass; omega
      rcases ha with ha | ha
      all_goals
        by_cases hp : b s = some (c,r) <;> simp [ha,hp] at ih ⊢ <;> omega
  simpa only [number,profile,total,countWhere,Bool.and_true] using hi squares

theorem I6_profile (b : Board) : I6 b ↔
    ∀ c, profile b 0 c (.native .bishop) ≤ 1 ∧ profile b 1 c (.native .bishop) ≤ 1 := by
  constructor
  · intro h c; exact ⟨h c 0 (by decide),h c 1 (by decide)⟩
  · intro h c a ha
    have he : a = 0 ∨ a = 1 := by omega
    rcases he with rfl | rfl
    · exact (h c).1
    · exact (h c).2

theorem I7_profile (b : Board) : I7 b ↔ ∀ c, profile b 0 c (.native .kirin) = 0 := by
  constructor
  · intro h c
    unfold profile countWhere
    have he : (squares.filter fun s => decide (b s = some (c,.native .kirin)) && decide (squareClass s = 0)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro s _
      by_cases hp : b s = some (c,.native .kirin)
      · simp [hp,h s c hp]
      · simp [hp]
    rw [he]
    rfl
  · intro h s c hp
    have ha : squareClass s = 0 ∨ squareClass s = 1 := by unfold squareClass; omega
    rcases ha with ha | ha
    · have hm : s ∈ squares.filter (fun t => decide (b t = some (c,.native .kirin)) && decide (squareClass t = 0)) := by
        simp [mem_squares,hp,ha]
      have he := h c
      have hnil := List.eq_nil_of_length_eq_zero he
      rw [hnil] at hm
      simp at hm
    · exact ha

def Material (n : Counts) : Prop := ∀ c,
  (∀ k : Separate, n c (.native k.base) + n c (.promoted k) ≤ initialSeparate k) ∧
  n c (.native .elephant) ≤ 1 ∧
  n c (.native .king) + n c (.native .elephant) ≤ 2 ∧
  n c (.native .kirin) ≤ 1 ∧ n c (.native .kirin) + n c (.native .lion) ≤ 2 ∧
  n c (.native .phoenix) ≤ 1 ∧ n c (.native .phoenix) + n c (.native .freeKing) ≤ 2

def Conditions (s : Summary) (n0 n1 : Counts) : Prop :=
  let n := total n0 n1
  n .black (.promoted .pawn) + n .white (.promoted .pawn) ≤ s.joint ∧
  (∀ c k, k ≠ .pawn → n c (.promoted (kindSeparate k)) ≤ cap s c k) ∧
  (∀ c, n0 c (.native .bishop) ≤ 1 ∧ n1 c (.native .bishop) ≤ 1) ∧
  (∀ c, n0 c (.native .kirin) = 0) ∧
  0 < n .white (.native .king) ∧ Material n

/-- The concrete arithmetic profile conditions are exactly the existing completion
conditions, including material and both square-colour restrictions. -/
theorem conditions_iff (s : Summary) (b : Board) :
    FreeConditions s b ↔ Conditions s (profile b 0) (profile b 1) := by
  simp only [FreeConditions,Bounds,Conditions,Material,I6_profile,I7_profile,
    I8,hasRoyal,I9,promotedNumber,kindSeparate,number_profile,and_assoc]

theorem number_zero_iff (b : Board) (c : Colour) (r : Role) :
    number b c r = 0 ↔ ∀ s, b s ≠ some (c,r) := by
  constructor
  · intro hz s hs
    have hm : s ∈ squares.filter (fun t => decide (b t = some (c,r)) && true) := by
      simp [mem_squares,hs]
    have he := List.eq_nil_of_length_eq_zero hz
    rw [he] at hm
    simp at hm
  · intro h
    unfold number countWhere
    have he : (squares.filter fun s => decide (b s = some (c,r)) && true) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro s _
      simp [h s]
    rw [he]
    rfl

def FreeRoles (n0 n1 : Counts) : Prop :=
  ∀ c k, n0 c (.native (kindBase k)) = 0 ∧ n1 c (.native (kindBase k)) = 0

theorem onlyFree_profile (b : Board) : OnlyFree b ↔ FreeRoles (profile b 0) (profile b 1) := by
  have hz : OnlyFree b ↔ ∀ c k, number b c (.native (kindBase k)) = 0 := by
    constructor
    · intro h c k
      apply (number_zero_iff b c _).mpr
      intro s hs
      have he := h s _ hs
      rw [isConfined_kind] at he
      cases he
    · intro h s p hp
      cases he : isConfined p.2 with
      | false => rfl
      | true =>
        obtain ⟨k,hk⟩ := (isConfined_iff p.2).mp he
        have hn := (number_zero_iff b p.1 _).mp (h p.1 k) s
        exact False.elim (hn (by simpa [← hk] using hp))
  rw [hz]
  unfold FreeRoles
  simp only [number_profile,total,Nat.add_eq_zero_iff]

def Mode (r : Bool) (n0 n1 : Counts) : Prop :=
  if r then 0 < total n0 n1 .black (.native .king) else ¬ 0 < total n0 n1 .black (.native .king)

theorem mode_profile (r : Bool) (b : Board) : RoyalMode r b ↔ Mode r (profile b 0) (profile b 1) := by
  cases r <;> simp only [RoyalMode,Mode,hasRoyal,number_profile]

def ValidProfile (r : Bool) (s : Summary) (n0 n1 : Counts) : Prop :=
  FreeRoles n0 n1 ∧ Conditions s n0 n1 ∧ Mode r n0 n1

/-- Actual stratum completions reduce to availability and this independent
arithmetic profile predicate; no group-state enumeration is assumed complete. -/
theorem completes_profile (r : Bool) (u f : Board) (hu : OnlyConfined u)
    (h1 : I1 u) (h2 : I2 u) (h3 : I3 u) :
    StratumCompletes r u f ↔ Disjoint u f ∧ ValidProfile r (boardSummary u) (profile f 0) (profile f 1) := by
  rw [stratum_iff r u f hu,completes_iff u f hu h1 h2 h3,
    onlyFree_profile,conditions_iff,mode_profile]
  unfold ValidProfile
  constructor
  · rintro ⟨⟨a,b,c⟩,d⟩; exact ⟨b,a,c,d⟩
  · rintro ⟨b,a,c,d⟩; exact ⟨⟨a,b,c⟩,d⟩

end ChuShogi.CompletionProfiles
