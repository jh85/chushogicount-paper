import ChuShogi.ConfigurationWeight

/-! Separate summary-independent free group choices from promoted-confined
multiplicities. This is a Cartesian product of canonical counts, not choices
of eligible origins, and is the next factorization of the checked EGF sum. -/
namespace ChuShogi.ConfigurationFactors
open Specification Promotion ConcreteDP SummaryBridge GroupCoverage GroupConfigurations FiniteConfigurations

structure PromotedChoice (s : Summary) where
  n : Colour → Kind → Nat
  black : n .black .pawn ≤ s.cb
  white : n .white .pawn ≤ s.cw
  joint : n .black .pawn+n .white .pawn ≤ s.joint
  nonpawn : ∀ c k, k ≠ .pawn → n c k ≤ cap s c k

def freePart (g : Config r s) : Config r zero where
  std := g.std
  royal := g.royal
  bishop := g.bishop
  kirin := g.kirin
  phoenix := g.phoenix
  promoted := fun _ _ => 0
  pawn_black := by rfl
  pawn_white := by rfl
  pawn_joint := by rfl
  nonpawn := fun _ _ _ => Nat.zero_le _

def promotedPart (g : Config r s) : PromotedChoice s :=
  ⟨g.promoted,g.pawn_black,g.pawn_white,g.pawn_joint,g.nonpawn⟩

def combine (f : Config r zero) (p : PromotedChoice s) : Config r s :=
  ⟨f.std,f.royal,f.bishop,f.kirin,f.phoenix,p.n,p.black,p.white,p.joint,p.nonpawn⟩

theorem free_promoted_zero (f : Config r zero) : f.promoted = fun _ _ => 0 := by
  funext c k
  by_cases hk : k = .pawn
  · subst k
    cases c with
    | black => have h := f.pawn_black; exact Nat.eq_zero_of_le_zero h
    | white => have h := f.pawn_white; exact Nat.eq_zero_of_le_zero h
  · have h := f.nonpawn c k hk
    have hz : cap zero c k = 0 := by cases c <;> cases k <;> rfl
    rw [hz] at h
    exact Nat.eq_zero_of_le_zero h

def equivalence (r : Bool) (s : Summary) : Config r s ≃ (Config r zero × PromotedChoice s) where
  toFun g := (freePart g,promotedPart g)
  invFun p := combine p.1 p.2
  left_inv g := by apply config_ext <;> rfl
  right_inv p := by
    apply Prod.ext
    · apply config_ext <;> first | rfl | exact (free_promoted_zero p.1).symm
    · cases p with
      | mk f p => cases p; rfl

theorem free_inputs (f : Config r zero) (p : PromotedChoice s) (c : Colour) :
    GroupWeights.configInputs (combine f p) c = GroupWeights.configInputs f c := by
  unfold GroupWeights.configInputs
  congr 1

theorem zero_sized : Sized zero := by
  refine ⟨by decide,?_,rfl,rfl⟩
  intro c k _
  cases c <;> cases k <;> decide

noncomputable instance freeFintype (r : Bool) : Fintype (Config r zero) := configFintype zero zero_sized r

noncomputable instance kindFintype : Fintype Kind :=
  Fintype.ofList [.pawn,.lance,.chariot,.goBetween] (by intro k; cases k <;> simp)

theorem promoted_bound (p : PromotedChoice s) (c : Colour) (k : Kind) : p.n c k < cap s c k+1 := by
  cases k with
  | pawn =>
    cases c with
    | black => have h := p.black; exact Nat.lt_succ_of_le h
    | white => have h := p.white; exact Nat.lt_succ_of_le h
  | lance | chariot | goBetween => exact Nat.lt_succ_of_le (p.nonpawn c _ (by decide))

def encode (p : PromotedChoice s) : (c : Colour) → (k : Kind) → Fin (cap s c k+1) :=
  fun c k => ⟨p.n c k,promoted_bound p c k⟩

theorem encode_injective : Function.Injective (encode (s := s)) := by
  intro p q h
  have hn : p.n = q.n := by
    funext c k
    exact congrArg Fin.val (congrFun (congrFun h c) k)
  cases p; cases q; cases hn; rfl

noncomputable instance promotedFintype (s : Summary) : Fintype (PromotedChoice s) :=
  Fintype.ofInjective encode encode_injective

/-- A checked factorization of any full canonical-configuration sum into its
free and promoted-confined choices. The later coefficient algorithm uses it
with the proved placement weight. -/
theorem sum_factor (r : Bool) (s : Summary) (hs : Sized s) (w : Config r s → ℚ) :
    letI := configFintype s hs r
    (∑ g : Config r s, w g) = ∑ f : Config r zero, ∑ p : PromotedChoice s, w (combine f p) := by
  let := configFintype s hs r
  have he := Fintype.sum_equiv (equivalence r s) w (fun p => w (combine p.1 p.2)) (fun _ => rfl)
  exact he.trans (Fintype.sum_prod_type _)

end ChuShogi.ConfigurationFactors
