import ChuShogi.Specification

/-! Free-group count states, specified on present canonical multiplicities.
These lemmas do not yet count placements of pieces on squares or prove the EGF.
-/
namespace ChuShogi.CanonicalGroups

/-- Ordinary promotable stock: each present unpromoted/promoted multiplicity once. -/
def stdStates (n : Nat) : List (Nat × Nat) :=
  (List.range (n + 1)).flatMap fun u => (List.range (n - u + 1)).map fun p => (u,p)

theorem stdStates_iff (n u p : Nat) : (u,p) ∈ stdStates n ↔ u + p ≤ n := by
  simp only [stdStates, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨v, hv, q, hq, rfl, rfl⟩
    omega
  · intro h
    exact ⟨u, by omega, p, by omega, rfl, rfl⟩

theorem stdStates_nodup (n : Nat) : (stdStates n).Nodup := by
  simp only [stdStates, List.nodup_iff_pairwise_ne, List.pairwise_flatMap,
    List.pairwise_map]
  constructor
  · intro u _
    apply List.Pairwise.imp _ List.nodup_range
    intro p q hpq heq
    exact hpq (Prod.mk.inj heq).2
  · apply List.Pairwise.imp _ List.nodup_range
    intro u v huv a ha b hb heq
    rcases List.mem_map.mp ha with ⟨p, _, rfl⟩
    rcases List.mem_map.mp hb with ⟨q, _, rfl⟩
    exact huv (Prod.mk.inj heq).1

/-- Canonical king/elephant multiplicities; crown princes are kings here. -/
def RoyalMaterial (k e : Nat) : Prop := e ≤ 1 ∧ k + e ≤ 2

def royalStates : List (Nat × Nat) := [(0,0), (0,1), (1,0), (1,1), (2,0)]

theorem royalStates_iff (k e : Nat) :
    (k,e) ∈ royalStates ↔ RoyalMaterial k e := by
  simp only [royalStates, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq, RoyalMaterial]
  omega

theorem royalStates_nodup : royalStates.Nodup := by decide

def requiredRoyalStates : List (Nat × Nat) := [(1,0), (1,1), (2,0)]
def noRoyalStates : List (Nat × Nat) := [(0,0), (0,1)]

theorem requiredRoyalStates_iff (k e : Nat) :
    (k,e) ∈ requiredRoyalStates ↔ RoyalMaterial k e ∧ 0 < k := by
  simp only [requiredRoyalStates, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq, RoyalMaterial]
  omega

theorem noRoyalStates_iff (k e : Nat) :
    (k,e) ∈ noRoyalStates ↔ RoyalMaterial k e ∧ k = 0 := by
  simp only [noRoyalStates, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq, RoyalMaterial]
  omega

/-- Explicit raw King/Elephant/Crown-prince origin assignments. -/
def RoyalOrigin (king elephant prince : Nat) : Prop :=
  king ≤ 1 ∧ elephant + prince ≤ 1

/-- Material on canonical roles is equivalent to existence of origin assignments. -/
theorem royal_origins_iff (k e : Nat) :
    RoyalMaterial k e ↔ ∃ king prince, RoyalOrigin king e prince ∧ k = king + prince := by
  unfold RoyalMaterial RoyalOrigin
  constructor
  · intro h
    by_cases hk : k = 2
    · exact ⟨1, 1, by omega, by omega⟩
    · exact ⟨k, 0, by omega, by omega⟩
  · rintro ⟨king, prince, h, hk⟩
    omega

/-- Two different raw origins really can specify the same canonical state. -/
theorem royal_origin_nonunique :
    RoyalOrigin 1 0 0 ∧ RoyalOrigin 0 0 1 ∧ 1 + 0 = (0 + 1 : Nat) := by unfold RoyalOrigin; decide

/-- Native kirin/phoenix plus its merged lion/free-king multiplicity. -/
def JumperMaterial (small big : Nat) : Prop := small ≤ 1 ∧ small + big ≤ 2

def jumperStates : List (Nat × Nat) := [(0,0), (0,1), (0,2), (1,0), (1,1)]

theorem jumperStates_iff (small big : Nat) :
    (small,big) ∈ jumperStates ↔ JumperMaterial small big := by
  simp only [jumperStates, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq, JumperMaterial]
  omega

theorem jumperStates_nodup : jumperStates.Nodup := by decide

/-- Unpromoted bishops per class and promoted bishops on unrestricted squares. -/
def BishopMaterial (u0 u1 p : Nat) : Prop := u0 ≤ 1 ∧ u1 ≤ 1 ∧ u0 + u1 + p ≤ 2

def bishopStates : List (Nat × Nat × Nat) :=
  [(0,0,0), (0,0,1), (0,0,2), (0,1,0), (0,1,1), (1,0,0), (1,0,1), (1,1,0)]

theorem bishopStates_iff (u0 u1 p : Nat) :
    (u0,u1,p) ∈ bishopStates ↔ BishopMaterial u0 u1 p := by
  simp only [bishopStates, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq, BishopMaterial]
  omega

theorem bishopStates_nodup : bishopStates.Nodup := by decide

end ChuShogi.CanonicalGroups
