import ChuShogi.GroupCoverage

/-! Canonical Cartesian choices. Each coordinate is a present piece-count
state, not an origin assignment. Unrestricted class splits are forgotten here;
the inverse laws apply to normalized profiles. Placement refinement must sum
those splits, rather than treating them as additional group states. -/
namespace ChuShogi.GroupConfigurations
open Specification Promotion ConcreteDP CompletionProfiles SummaryBridge CanonicalGroups GroupCoverage

abbrev Member (xs : List α) := {v : α // v ∈ xs}

structure Config (r : Bool) (s : Summary) where
  std : (c : Colour) → (k : Separate) → k ∈ ordinary → Member (stdStates 2)
  royal : (c : Colour) → Member (royalList r c)
  bishop : Colour → Member bishopStates
  kirin : Colour → Member jumperStates
  phoenix : Colour → Member jumperStates
  promoted : Colour → Kind → Nat
  pawn_black : promoted .black .pawn ≤ s.cb
  pawn_white : promoted .white .pawn ≤ s.cw
  pawn_joint : promoted .black .pawn + promoted .white .pawn ≤ s.joint
  nonpawn : ∀ c k, k ≠ .pawn → promoted c k ≤ cap s c k

theorem config_ext (g h : Config r s) (hs : g.std = h.std) (hr : g.royal = h.royal)
    (hb : g.bishop = h.bishop) (hk : g.kirin = h.kirin) (hp : g.phoenix = h.phoenix)
    (hc : g.promoted = h.promoted) : g = h := by
  cases g; cases h
  cases hs; cases hr; cases hb; cases hk; cases hp; cases hc
  rfl

def sep (g : Config r s) (c : Colour) (k : Separate) : Nat × Nat :=
  if h : k ∈ ordinary then (g.std c k h).val else
  match k with
  | .pawn => (0,g.promoted c .pawn)
  | .lance => (0,g.promoted c .lance)
  | .chariot => (0,g.promoted c .chariot)
  | .goBetween => (0,g.promoted c .goBetween)
  | .bishop => ((g.bishop c).val.1 + (g.bishop c).val.2.1,(g.bishop c).val.2.2)
  | _ => (0,0)

def counts (g : Config r s) (c : Colour) : Role → Nat
  | .native .pawn => (sep g c .pawn).1
  | .native .lance => (sep g c .lance).1
  | .native .chariot => (sep g c .chariot).1
  | .native .goBetween => (sep g c .goBetween).1
  | .native .gold => (sep g c .gold).1
  | .native .silver => (sep g c .silver).1
  | .native .copper => (sep g c .copper).1
  | .native .leopard => (sep g c .leopard).1
  | .native .tiger => (sep g c .tiger).1
  | .native .sideMover => (sep g c .sideMover).1
  | .native .verticalMover => (sep g c .verticalMover).1
  | .native .rook => (sep g c .rook).1
  | .native .dragonHorse => (sep g c .dragonHorse).1
  | .native .dragonKing => (sep g c .dragonKing).1
  | .native .bishop => (sep g c .bishop).1
  | .native .king => (g.royal c).val.1
  | .native .elephant => (g.royal c).val.2
  | .native .kirin => (g.kirin c).val.1
  | .native .lion => (g.kirin c).val.2
  | .native .phoenix => (g.phoenix c).val.1
  | .native .freeKing => (g.phoenix c).val.2
  | .promoted k => (sep g c k).2

def class0 (g : Config r s) (c : Colour) (p : Role) : Nat :=
  match p with
  | .native .bishop => (g.bishop c).val.1
  | .native .kirin => 0
  | _ => counts g c p

def class1 (g : Config r s) (c : Colour) (p : Role) : Nat :=
  match p with
  | .native .bishop => (g.bishop c).val.2.1
  | .native .kirin => (g.kirin c).val.1
  | _ => 0

theorem total_classes (g : Config r s) : total (class0 g) (class1 g) = counts g := by
  funext c p
  cases p with
  | native b => cases b <;> simp [total,class0,class1,counts,sep,ordinary]
  | promoted k => simp [total,class0,class1]

theorem counts_sep (g : Config r s) (c : Colour) (k : Separate) :
    counts g c (.native k.base) = (sep g c k).1 := by cases k <;> rfl

theorem grouped_classes (g : Config r s) : Grouped r s (class0 g) (class1 g) := by
  simp only [Grouped,total_classes]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro c k
    cases k <;> simp [class0,class1,counts,sep,ordinary,kindBase]
  · exact ⟨g.pawn_black,g.pawn_white,g.pawn_joint,by
      intro c k hk; cases k <;> first | exact g.nonpawn c _ (by decide) | contradiction⟩
  · intro c k hk
    rw [counts_sep]
    change ((sep g c k).1,(sep g c k).2) ∈ stdStates 2
    simpa only [sep,dite_eq_left hk] using (g.std c k hk).property
  · intro c
    exact (g.royal c).property
  · intro c
    exact (g.bishop c).property
  · intro c
    exact ⟨(g.kirin c).property,rfl⟩
  · intro c
    exact (g.phoenix c).property

def ofGrouped (n0 n1 : Counts) (h : Grouped r s n0 n1) : Config r s where
  std c k hk := ⟨(total n0 n1 c (.native k.base),total n0 n1 c (.promoted k)),h.2.2.1 c k hk⟩
  royal c := ⟨(total n0 n1 c (.native .king),total n0 n1 c (.native .elephant)),h.2.2.2.1 c⟩
  bishop c := ⟨(n0 c (.native .bishop),n1 c (.native .bishop),total n0 n1 c (.promoted .bishop)),h.2.2.2.2.1 c⟩
  kirin c := ⟨(total n0 n1 c (.native .kirin),total n0 n1 c (.native .lion)),(h.2.2.2.2.2.1 c).1⟩
  phoenix c := ⟨(total n0 n1 c (.native .phoenix),total n0 n1 c (.native .freeKing)),h.2.2.2.2.2.2 c⟩
  promoted c k := total n0 n1 c (.promoted (kindSeparate k))
  pawn_black := h.2.1.1
  pawn_white := h.2.1.2.1
  pawn_joint := h.2.1.2.2.1
  nonpawn := h.2.1.2.2.2

theorem counts_ofGrouped (n0 n1 : Counts) (h : Grouped r s n0 n1) :
    counts (ofGrouped n0 n1 h) = total n0 n1 := by
  have hz c k : total n0 n1 c (.native (kindBase k)) = 0 := by
    simp only [total,(h.1 c k).1,(h.1 c k).2,Nat.add_zero]
  funext c p
  cases p with
  | native b =>
    cases b <;> simp [counts,sep,ofGrouped,ordinary,total,Separate.base]
    · exact (hz c .pawn).symm
    · exact (hz c .lance).symm
    · exact (hz c .chariot).symm
    · exact (hz c .goBetween).symm
  | promoted k => cases k <;> simp [counts,sep,ofGrouped,ordinary,kindSeparate]

theorem roundtrip (g : Config r s) :
    ofGrouped (class0 g) (class1 g) (grouped_classes g) = g := by
  apply config_ext
  · funext c k hk
    apply Subtype.ext
    change (total (class0 g) (class1 g) c (.native k.base),
      total (class0 g) (class1 g) c (.promoted k)) = (g.std c k hk).val
    rw [total_classes,counts_sep]
    change ((sep g c k).1,(sep g c k).2) = (g.std c k hk).val
    simp only [sep,dite_eq_left hk]
  · funext c; apply Subtype.ext; simp only [ofGrouped,total_classes,counts]
  · funext c; apply Subtype.ext
    simp [ofGrouped,class0,class1,total_classes,counts,sep,ordinary]
  · funext c; apply Subtype.ext; simp only [ofGrouped,total_classes,counts]
  · funext c; apply Subtype.ext; simp only [ofGrouped,total_classes,counts]
  · funext c k
    simp only [ofGrouped,total_classes]
    cases k <;> simp [counts,sep,ordinary,kindSeparate]

/-- Canonical choices determine, and are determined by, the unrestricted totals
and the two bishop class counts. No origin multiplicity appears. -/
theorem canonical_injective (g h : Config r s)
    (h0 : class0 g = class0 h) (h1 : class1 g = class1 h) : g = h := by
  have hg := roundtrip g
  simp only [h0,h1] at hg
  exact hg.symm.trans (roundtrip h)

theorem freeRoles_total (n0 n1 : Counts) : FreeRoles n0 n1 ↔
    ∀ c k, total n0 n1 c (.native (kindBase k)) = 0 := by
  simp only [FreeRoles,total,Nat.add_eq_zero_iff]

theorem grouped_congr (a0 a1 b0 b1 : Counts)
    (ht : total a0 a1 = total b0 b1)
    (hb0 : ∀ c, a0 c (.native .bishop) = b0 c (.native .bishop))
    (hb1 : ∀ c, a1 c (.native .bishop) = b1 c (.native .bishop))
    (hk0 : ∀ c, a0 c (.native .kirin) = b0 c (.native .kirin)) :
    Grouped r s a0 a1 ↔ Grouped r s b0 b1 := by
  simp only [Grouped,freeRoles_total,ht,hb0,hb1,hk0]

/-- One canonical state; the unrestricted class splits remain placement data. -/
def Represents (g : Config r s) (n0 n1 : Counts) : Prop :=
  counts g = total n0 n1 ∧
  (∀ c, (g.bishop c).val.1 = n0 c (.native .bishop)) ∧
  (∀ c, (g.bishop c).val.2.1 = n1 c (.native .bishop)) ∧
  ∀ c, n0 c (.native .kirin) = 0

theorem represents_grouped (g : Config r s) (n0 n1 : Counts) (h : Represents g n0 n1) :
    Grouped r s n0 n1 := by
  exact (grouped_congr (class0 g) (class1 g) n0 n1
    ((total_classes g).trans h.1) h.2.1 h.2.2.1 (fun c => (h.2.2.2 c).symm)).mp (grouped_classes g)

theorem represents_unique (g h : Config r s) (n0 n1 : Counts)
    (hg : Represents g n0 n1) (hh : Represents h n0 n1) : g = h := by
  have hn : counts g = counts h := hg.1.trans hh.1.symm
  apply canonical_injective
  · funext c p
    cases p with
    | native b =>
      cases b <;> simp only [class0] <;> first
        | exact (hg.2.1 c).trans (hh.2.1 c).symm
        | rfl
        | exact congrFun (congrFun hn c) _
    | promoted k => exact congrFun (congrFun hn c) (.promoted k)
  · funext c p
    cases p with
    | native b =>
      cases b <;> simp only [class1] <;> first
        | exact (hg.2.2.1 c).trans (hh.2.2.1 c).symm
        | exact congrFun (congrFun hn c) (.native .kirin)
    | promoted k => rfl

/-- Complete arithmetic coverage, with exactly one canonical group choice.
This theorem counts no alternative king/crown-prince or jumper origins. -/
theorem grouped_unique (n0 n1 : Counts) :
    Grouped r s n0 n1 ↔ ∃! g : Config r s, Represents g n0 n1 := by
  constructor
  · intro h
    refine ⟨ofGrouped n0 n1 h,⟨counts_ofGrouped n0 n1 h,?_,?_,?_⟩,?_⟩
    · intro c; rfl
    · intro c; rfl
    · intro c; exact (h.2.2.2.2.2.1 c).2
    · intro g hg
      exact represents_unique g _ n0 n1 hg ⟨counts_ofGrouped n0 n1 h,(fun _ => rfl),(fun _ => rfl),
        fun c => (h.2.2.2.2.2.1 c).2⟩
  · rintro ⟨g,hg,_⟩
    exact represents_grouped g n0 n1 hg

theorem valid_unique (s : Summary) (hs : Sized s) (r : Bool) (n0 n1 : Counts) :
    ValidProfile r s n0 n1 ↔ ∃! g : Config r s, Represents g n0 n1 :=
  (grouped_iff r s hs n0 n1).symm.trans (grouped_unique n0 n1)

theorem valid_compact_unique (s : Summary) (hs : CompactSummary.RealizedCompact s)
    (r : Bool) (n0 n1 : Counts) :
    ValidProfile r s n0 n1 ↔ ∃! g : Config r s, Represents g n0 n1 :=
  valid_unique s (sized_compact_realized s hs) r n0 n1

end ChuShogi.GroupConfigurations
