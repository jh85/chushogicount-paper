import ChuShogi.GroupWeights
import ChuShogi.AlphabetRestriction
import ChuShogi.TwoClassEGF

/-! Concrete present bound labels and unrestricted canonical roles. A label is
a colour and present role/class, never an original bishop/kirin identity.
The two bishops of one colour are distinguished by square class only. -/
namespace ChuShogi.CanonicalAlphabet
open Specification Promotion CompletionProfiles CanonicalGroups GroupConfigurations
open AlphabetRestriction
open scoped Classical

noncomputable instance colourFintype : Fintype Colour :=
  Fintype.ofList [.black,.white] (by intro c; cases c <;> simp)

noncomputable instance pieceFintype : Fintype Piece :=
  Fintype.ofInjective (fun p : Piece => some p) (Option.some_injective Piece)

def IsUnbound (p : Piece) : Prop := p.2 ≠ .native .bishop ∧ p.2 ≠ .native .kirin
abbrev Unbound := {p : Piece // IsUnbound p}

noncomputable instance unboundFintype : Fintype Unbound := Fintype.ofFinite _

def bishopCount (g : Config r s) (a : Bool) (c : Colour) : Nat :=
  if a then (g.bishop c).val.2.1 else (g.bishop c).val.1

abbrev BishopLabel (g : Config r s) (a : Bool) := {c : Colour // bishopCount g a c = 1}
abbrev KirinLabel (g : Config r s) := {c : Colour // (g.kirin c).val.1 = 1}
abbrev Bound0 (g : Config r s) := BishopLabel g false
abbrev Bound1 (g : Config r s) := BishopLabel g true ⊕ KirinLabel g

def bishopEmbedding (g : Config r s) (a : Bool) : BishopLabel g a ↪ Piece where
  toFun c := (c.val,.native .bishop)
  inj' := fun _ _ h => Subtype.ext (Prod.mk.inj h).1

def kirinEmbedding (g : Config r s) : KirinLabel g ↪ Piece where
  toFun c := (c.val,.native .kirin)
  inj' := fun _ _ h => Subtype.ext (Prod.mk.inj h).1

def unboundEmbedding : Unbound ↪ Piece := ⟨Subtype.val,Subtype.val_injective⟩

def bound1Embedding (g : Config r s) : Bound1 g ↪ Piece :=
  sumEmbedding (bishopEmbedding g true) (kirinEmbedding g) (by
    intro b k h
    have hh : Role.native .bishop = .native .kirin := congrArg Prod.snd h
    cases hh)

def code0 (g : Config r s) : Bound0 g ⊕ Unbound ↪ Piece :=
  sumEmbedding (bishopEmbedding g false) unboundEmbedding (by
    intro b p h
    exact p.property.1 (congrArg Prod.snd h).symm)

def code1 (g : Config r s) : Bound1 g ⊕ Unbound ↪ Piece :=
  sumEmbedding (bound1Embedding g) unboundEmbedding (by
    intro b p h
    cases b with
    | inl b => exact p.property.1 (congrArg Prod.snd h).symm
    | inr k => exact p.property.2 (congrArg Prod.snd h).symm)

theorem card_colour_ones (n : Colour → Nat) (h : ∀ c, n c ≤ 1) :
    Fintype.card {c : Colour // n c = 1} = n .black+n .white := by
  have hu : (Finset.univ : Finset Colour) = {.black,.white} := by
    ext c; cases c <;> simp
  rw [Fintype.card_subtype,hu]
  have hb : n .black = 0 ∨ n .black = 1 := by have := h .black; omega
  have hw : n .white = 0 ∨ n .white = 1 := by have := h .white; omega
  rcases hb with hb | hb <;> rcases hw with hw | hw <;>
    simp [Finset.filter_insert,Finset.filter_singleton,hb,hw]

theorem bishop_card (g : Config r s) (a : Bool) :
    Fintype.card (BishopLabel g a) = bishopCount g a .black+bishopCount g a .white := by
  apply card_colour_ones
  intro c
  have hb := (bishopStates_iff _ _ _).mp (g.bishop c).property
  cases a
  · exact hb.1
  · exact hb.2.1

theorem kirin_card (g : Config r s) :
    Fintype.card (KirinLabel g) = (g.kirin .black).val.1+(g.kirin .white).val.1 := by
  apply card_colour_ones
  intro c
  exact ((jumperStates_iff _ _).mp (g.kirin c).property).1

theorem bound0_card (g : Config r s) : Fintype.card (Bound0 g) =
    (g.bishop .black).val.1+(g.bishop .white).val.1 := bishop_card g false

theorem bound1_card (g : Config r s) : Fintype.card (Bound1 g) =
    (g.bishop .black).val.2.1+(g.bishop .white).val.2.1+
      ((g.kirin .black).val.1+(g.kirin .white).val.1) := by
  rw [Fintype.card_sum,bishop_card,kirin_card]
  rfl

def unboundCounts (g : Config r s) (p : Unbound) : Nat := counts g p.val.1 p.val.2

theorem code0_range (g : Config r s) (p : Piece) : p ∈ Set.range (code0 g) ↔
    IsUnbound p ∨ (p.2 = .native .bishop ∧ bishopCount g false p.1 = 1) := by
  rcases p with ⟨c,t⟩
  constructor
  · rintro ⟨v,hv⟩
    cases v with
    | inl b =>
      change (b.val,Role.native .bishop) = (c,t) at hv
      obtain ⟨hc,ht⟩ := Prod.mk.inj hv
      exact .inr ⟨ht.symm,hc ▸ b.property⟩
    | inr p => exact .inl (hv ▸ p.property)
  · rintro (hp | ⟨ht,hc⟩)
    · exact ⟨.inr ⟨(c,t),hp⟩,rfl⟩
    · change t = .native .bishop at ht
      subst t
      exact ⟨.inl ⟨c,hc⟩,rfl⟩

theorem code1_range (g : Config r s) (p : Piece) : p ∈ Set.range (code1 g) ↔
    IsUnbound p ∨ (p.2 = .native .bishop ∧ bishopCount g true p.1 = 1) ∨
      (p.2 = .native .kirin ∧ (g.kirin p.1).val.1 = 1) := by
  rcases p with ⟨c,t⟩
  constructor
  · rintro ⟨v,hv⟩
    cases v with
    | inl b =>
      cases b with
      | inl b =>
        change (b.val,Role.native .bishop) = (c,t) at hv
        obtain ⟨hc,ht⟩ := Prod.mk.inj hv
        exact .inr (.inl ⟨ht.symm,hc ▸ b.property⟩)
      | inr k =>
        change (k.val,Role.native .kirin) = (c,t) at hv
        obtain ⟨hc,ht⟩ := Prod.mk.inj hv
        exact .inr (.inr ⟨ht.symm,hc ▸ k.property⟩)
    | inr p => exact .inl (hv ▸ p.property)
  · rintro (hp | ⟨ht,hc⟩ | ⟨ht,hc⟩)
    · exact ⟨.inr ⟨(c,t),hp⟩,rfl⟩
    · change t = .native .bishop at ht
      subst t
      exact ⟨.inl (.inl ⟨c,hc⟩),rfl⟩
    · change t = .native .kirin at ht
      subst t
      exact ⟨.inl (.inr ⟨c,hc⟩),rfl⟩

/-- The complete canonical profile fibre: class-specific bound counts and
unrestricted total counts, with no lost ordinary or promoted roles. -/
theorem represents_iff (g : Config r s) (n0 n1 : Counts) : Represents g n0 n1 ↔
    (∀ c, n0 c (.native .bishop) = (g.bishop c).val.1 ∧
      n1 c (.native .bishop) = (g.bishop c).val.2.1 ∧
      n0 c (.native .kirin) = 0 ∧ n1 c (.native .kirin) = (g.kirin c).val.1) ∧
    ∀ p : Unbound, total n0 n1 p.val.1 p.val.2 = unboundCounts g p := by
  constructor
  · intro h
    refine ⟨?_,fun p => (congrFun (congrFun h.1 p.val.1) p.val.2).symm⟩
    intro c
    refine ⟨(h.2.1 c).symm,(h.2.2.1 c).symm,h.2.2.2 c,?_⟩
    have he := congrFun (congrFun h.1 c) (.native .kirin)
    change (g.kirin c).val.1 = n0 c (.native .kirin)+n1 c (.native .kirin) at he
    rw [h.2.2.2 c,Nat.zero_add] at he
    exact he.symm
  · rintro ⟨h,hfree⟩
    refine ⟨?_,(fun c => (h c).1.symm),(fun c => (h c).2.1.symm),fun c => (h c).2.2.1⟩
    funext c p
    by_cases hb : p = .native .bishop
    · subst p
      change (sep g c .bishop).1 = n0 c (.native .bishop)+n1 c (.native .bishop)
      simp only [sep,dite_eq_right (show Separate.bishop ∉ GroupCoverage.ordinary by decide)]
      rw [(h c).1,(h c).2.1]
    · by_cases hk : p = .native .kirin
      · subst p
        change (g.kirin c).val.1 = n0 c (.native .kirin)+n1 c (.native .kirin)
        rw [(h c).2.2.1,(h c).2.2.2,Nat.zero_add]
      · exact (hfree ⟨(c,p),hb,hk⟩).symm

end ChuShogi.CanonicalAlphabet
