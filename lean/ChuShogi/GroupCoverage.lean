import ChuShogi.ProfileCount
import ChuShogi.CanonicalGroups

/-! Exact arithmetic coverage by the source's canonical group states.
Unrestricted square-class splits are retained in the input profiles and will be
summed by placement refinement; group states record canonical multiplicities,
never possible origin assignments. -/
namespace ChuShogi.GroupCoverage
open Specification Promotion ConcreteDP CompletionProfiles SummaryBridge CanonicalGroups

/-- The ten ordinary, two-stock, separately promotable free groups per side. -/
def ordinary : List Separate :=
  [.gold,.silver,.copper,.leopard,.tiger,.sideMover,.verticalMover,.rook,.dragonHorse,.dragonKing]

def royalList (r : Bool) (c : Colour) : List (Nat × Nat) :=
  if c = .white then requiredRoyalStates else if r then requiredRoyalStates else noRoyalStates

def NeedKing (r : Bool) (c : Colour) (k : Nat) : Prop :=
  if c = .white then 0 < k else if r then 0 < k else k = 0

theorem royalList_iff (r : Bool) (c : Colour) (k e : Nat) :
    (k,e) ∈ royalList r c ↔ RoyalMaterial k e ∧ NeedKing r c k := by
  cases c <;> cases r <;> simp [royalList,NeedKing,requiredRoyalStates_iff,noRoyalStates_iff]

/-- These arithmetic facts hold for every actual DP summary. -/
def Sized (s : Summary) : Prop :=
  s.joint ≤ 12 ∧ (∀ c k, k ≠ .pawn → cap s c k ≤ 2) ∧ s.cb = s.joint ∧ s.cw = s.joint

def PromotedBounds (s : Summary) (n : Counts) : Prop :=
  n .black (.promoted .pawn) ≤ s.cb ∧ n .white (.promoted .pawn) ≤ s.cw ∧
  n .black (.promoted .pawn) + n .white (.promoted .pawn) ≤ s.joint ∧
  ∀ c k, k ≠ .pawn → n c (.promoted (kindSeparate k)) ≤ cap s c k

/-- Cartesian group membership, extracted from present canonical count profiles. -/
def Grouped (r : Bool) (s : Summary) (n0 n1 : Counts) : Prop :=
  let n := total n0 n1
  FreeRoles n0 n1 ∧ PromotedBounds s n ∧
  (∀ c k, k ∈ ordinary → (n c (.native k.base),n c (.promoted k)) ∈ stdStates 2) ∧
  (∀ c, (n c (.native .king),n c (.native .elephant)) ∈ royalList r c) ∧
  (∀ c, (n0 c (.native .bishop),n1 c (.native .bishop),n c (.promoted .bishop)) ∈ bishopStates) ∧
  (∀ c, (n c (.native .kirin),n c (.native .lion)) ∈ jumperStates ∧ n0 c (.native .kirin) = 0) ∧
  (∀ c, (n c (.native .phoenix),n c (.native .freeKing)) ∈ jumperStates)

theorem ordinary_stock (k : Separate) (h : k ∈ ordinary) : initialSeparate k = 2 := by
  cases k <;> first | rfl | simp [ordinary] at h

/-- Exact coverage for all arithmetic profiles, not just sampled or listed ones. -/
theorem grouped_iff (r : Bool) (s : Summary) (hs : Sized s) (n0 n1 : Counts) :
    Grouped r s n0 n1 ↔ ValidProfile r s n0 n1 := by
  let n := total n0 n1
  constructor
  · rintro ⟨hfree,hp,hstd,hroy,hbish,hkir,hpho⟩
    have hr (c) := (royalList_iff r c _ _).mp (hroy c)
    have hb (c) := (bishopStates_iff _ _ _).mp (hbish c)
    have hk (c) := (jumperStates_iff _ _).mp (hkir c).1
    have hx (c) := (jumperStates_iff _ _).mp (hpho c)
    have hz (c : Colour) (k : Kind) : n c (.native (kindBase k)) = 0 := by
      dsimp [n,total]
      rw [(hfree c k).1,(hfree c k).2]
    have hconf (c : Colour) (k : Kind) : n c (.native (kindBase k)) + n c (.promoted (kindSeparate k)) ≤ ConfinedMaterial.stock k := by
      rw [hz]
      by_cases he : k = .pawn
      · subst k
        have hj := hp.2.2.1
        change n .black (.promoted .pawn) + n .white (.promoted .pawn) ≤ s.joint at hj
        have hjmax := hs.1
        cases c <;> simp only [kindSeparate,ConfinedMaterial.stock,ite_true,Nat.zero_add] <;> omega
      · have hc := hp.2.2.2 c k he
        change n c (.promoted (kindSeparate k)) ≤ cap s c k at hc
        have hcmax := hs.2.1 c k he
        simp only [ConfinedMaterial.stock,he,ite_false,Nat.zero_add]
        omega
    have hm : Material n := by
      intro c
      refine ⟨?_,(hr c).1.1,(hr c).1.2,(hk c).1,(hk c).2,(hx c).1,(hx c).2⟩
      intro k
      cases k with
      | pawn => exact hconf c .pawn
      | lance => exact hconf c .lance
      | chariot => exact hconf c .chariot
      | goBetween => exact hconf c .goBetween
      | bishop => exact (hb c).2.2
      | gold | silver | copper | leopard | tiger | sideMover | verticalMover | rook | dragonHorse | dragonKing =>
        exact (stdStates_iff _ _ _).mp (hstd c _ (by decide))
    have hw : 0 < n .white (.native .king) := by simpa [NeedKing] using (hr .white).2
    have hmode : Mode r n0 n1 := by
      have hh := (hr .black).2
      change (if r then 0 < n .black (.native .king) else ¬ 0 < n .black (.native .king))
      cases r <;> simp [NeedKing] at hh ⊢ <;> omega
    exact ⟨hfree,⟨hp.2.2.1,hp.2.2.2,(fun c => ⟨(hb c).1,(hb c).2.1⟩),
      (fun c => (hkir c).2),hw,hm⟩,hmode⟩
  · rintro ⟨hfree,⟨hjoint,hcaps,hbish,hkir,hw,hmat⟩,hmode⟩
    have hm : Material n := hmat
    have hroy (c : Colour) : (n c (.native .king),n c (.native .elephant)) ∈ royalList r c := by
      apply (royalList_iff r c _ _).mpr
      refine ⟨⟨(hm c).2.1,(hm c).2.2.1⟩,?_⟩
      cases c with
      | white => exact hw
      | black =>
        change (if r then 0 < n .black (.native .king) else ¬ 0 < n .black (.native .king)) at hmode
        cases r <;> simp [NeedKing] at hmode ⊢ <;> omega
    refine ⟨hfree,⟨?_,?_,hjoint,hcaps⟩,?_,hroy,?_,?_,?_⟩
    · change n .black (.promoted .pawn) ≤ s.cb
      change n .black (.promoted .pawn) + n .white (.promoted .pawn) ≤ s.joint at hjoint
      have he := hs.2.2.1; omega
    · change n .white (.promoted .pawn) ≤ s.cw
      change n .black (.promoted .pawn) + n .white (.promoted .pawn) ≤ s.joint at hjoint
      have he := hs.2.2.2; omega
    · intro c k hk
      apply (stdStates_iff _ _ _).mpr
      rw [← ordinary_stock k hk]
      exact (hm c).1 k
    · intro c
      apply (bishopStates_iff _ _ _).mpr
      exact ⟨(hbish c).1,(hbish c).2,(hm c).1 .bishop⟩
    · intro c
      exact ⟨(jumperStates_iff _ _).mpr ⟨(hm c).2.2.2.1,(hm c).2.2.2.2.1⟩,hkir c⟩
    · intro c
      exact (jumperStates_iff _ _).mpr ⟨(hm c).2.2.2.2.2.1,(hm c).2.2.2.2.2.2⟩

theorem sized_board (b : Board) (h1 : I1 b) : Sized (boardSummary b) := by
  have hj : (boardSummary b).joint ≤ 12 := by
    rw [boardSummary_joint b h1]
    have h := List.length_filter_le
      (fun x : Fin 12 => decide (unpromoted b x .black .pawn = 0 ∧ unpromoted b x .white .pawn = 0)) (List.finRange 12)
    simpa only [pawnFiles,List.length_finRange] using h
  have hc (c : Colour) (k : Kind) (hk : k ≠ .pawn) : cap (boardSummary b) c k ≤ 2 := by
    rw [boardSummary_cap b h1]
    have h := ConfinedMaterial.native_capacity_bound b h1 c k
    simp only [ConfinedMaterial.stock,hk,ite_false] at h
    omega
  have hp (c : Colour) : cap (boardSummary b) c .pawn = (boardSummary b).joint := by
    rw [boardSummary_cap b h1,ConfinedMaterial.pawn_pool_eq,boardSummary_joint b h1]
  exact ⟨hj,hc,hp .black,hp .white⟩

theorem sized_realized (s : Summary) (h : StructuralCount.Realized s) : Sized s := by
  obtain ⟨us,hu,hs⟩ := h
  have hb := StructuralDecomposition.renderAny_valid us hu
  have he : boardSummary (StructuralDecomposition.renderAny us) = s :=
    (StructuralCount.summary_renderAny us hu).trans hs
  rw [← he]
  exact sized_board _ hb.2.1

theorem sized_erase (s : Summary) (h : Sized s) : Sized (CompactSummary.erase s) := by
  have he (c : Colour) (k : Kind) : cap (CompactSummary.erase s) c k = cap s c k := by cases c <;> cases k <;> rfl
  exact ⟨h.1, (fun c k hk => by rw [he]; exact h.2.1 c k hk), h.2.2⟩

theorem sized_compact_realized (s : Summary) (h : CompactSummary.RealizedCompact s) : Sized s := by
  obtain ⟨us,hu,rfl⟩ := h
  rw [CompactSummary.summary_compact]
  exact sized_erase _ (sized_realized _ ⟨us,hu,rfl⟩)

/-- Application coverage has no unproved summary-size premise. -/
theorem grouped_realized (r : Bool) (s : Summary) (h : StructuralCount.Realized s) (n0 n1 : Counts) :
    Grouped r s n0 n1 ↔ ValidProfile r s n0 n1 := grouped_iff r s (sized_realized s h) n0 n1

theorem grouped_compact_realized (r : Bool) (s : Summary) (h : CompactSummary.RealizedCompact s) (n0 n1 : Counts) :
    Grouped r s n0 n1 ↔ ValidProfile r s n0 n1 := grouped_iff r s (sized_compact_realized s h) n0 n1

theorem royalList_nodup (r : Bool) (c : Colour) : (royalList r c).Nodup := by
  cases c <;> cases r <;> decide

end ChuShogi.GroupCoverage

