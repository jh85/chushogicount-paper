import ChuShogi.CanonicalAlphabet

/-! Application of the two-class alphabet to the actual arithmetic profile
fibres. This connects canonical group choices to bound/unrestricted word data.
-/
namespace ChuShogi.CanonicalWordProfiles
open Specification Promotion CompletionProfiles GroupConfigurations CanonicalAlphabet
open AlphabetRestriction MultinomialPlacements BoundPlacements
open scoped Classical

variable {S0 S1 : Type} [Fintype S0] [Fintype S1]

def wordCounts {S : Type} [Fintype S] (w : S → Option Piece) : Counts :=
  fun c p => multiplicity w (some (c,p))

abbrev Words (g : Config r s) :=
  (S0 → Option (Bound0 g ⊕ Unbound)) × (S1 → Option (Bound1 g ⊕ Unbound))

theorem bishop0_count (g : Config r s) (w : S0 → Option (Bound0 g ⊕ Unbound))
    (h : Good w) (c : Colour) :
    wordCounts (extend (code0 g) w) c (.native .bishop) = (g.bishop c).val.1 := by
  apply bound_symbol_count (code0 g) w h
  · exact ((CanonicalGroups.bishopStates_iff _ _ _).mp (g.bishop c).property).1
  · rw [code0_range g (c,.native .bishop)]
    simp [IsUnbound,bishopCount]
  · intro p he
    exact p.property.1 (congrArg Prod.snd he)

theorem bishop1_count (g : Config r s) (w : S1 → Option (Bound1 g ⊕ Unbound))
    (h : Good w) (c : Colour) :
    wordCounts (extend (code1 g) w) c (.native .bishop) = (g.bishop c).val.2.1 := by
  apply bound_symbol_count (code1 g) w h
  · exact ((CanonicalGroups.bishopStates_iff _ _ _).mp (g.bishop c).property).2.1
  · rw [code1_range g (c,.native .bishop)]
    simp [IsUnbound,bishopCount]
  · intro p he
    exact p.property.1 (congrArg Prod.snd he)

theorem kirin0_count (g : Config r s) (w : S0 → Option (Bound0 g ⊕ Unbound)) (c : Colour) :
    wordCounts (extend (code0 g) w) c (.native .kirin) = 0 := by
  apply (supported_iff_zero (code0 g) _).mp (extend_supported _ _)
  rw [code0_range g (c,.native .kirin)]
  simp [IsUnbound]

theorem kirin1_count (g : Config r s) (w : S1 → Option (Bound1 g ⊕ Unbound))
    (h : Good w) (c : Colour) :
    wordCounts (extend (code1 g) w) c (.native .kirin) = (g.kirin c).val.1 := by
  apply bound_symbol_count (code1 g) w h
  · exact ((CanonicalGroups.jumperStates_iff _ _).mp (g.kirin c).property).1
  · rw [code1_range g (c,.native .kirin)]
    simp [IsUnbound]
  · intro p he
    exact p.property.2 (congrArg Prod.snd he)

/-- For actual coded canonical words, the profile fibre is exactly the
singleton bound-label conditions and unrestricted total-count conditions. -/
theorem represents_words (g : Config r s) (w : Words (S0 := S0) (S1 := S1) g) :
    Represents g (wordCounts (extend (code0 g) w.1)) (wordCounts (extend (code1 g) w.2)) ↔
      TwoClassEGF.GoodPair w ∧ TwoClassEGF.Counts (unboundCounts g) w := by
  rw [CanonicalAlphabet.represents_iff]
  constructor
  · rintro ⟨hb,hn⟩
    refine ⟨⟨?_,?_⟩,?_⟩
    · apply (good_iff_counts w.1).mpr
      intro x
      have he := extend_multiplicity (code0 g) w.1 (.inl x)
      have hx := (hb x.val).1
      exact he.symm.trans (hx.trans x.property)
    · apply (good_iff_counts w.2).mpr
      intro x
      cases x with
      | inl b =>
        have he := extend_multiplicity (code1 g) w.2 (.inl (.inl b))
        exact he.symm.trans (((hb b.val).2.1).trans b.property)
      | inr k =>
        have he := extend_multiplicity (code1 g) w.2 (.inl (.inr k))
        exact he.symm.trans (((hb k.val).2.2.2).trans k.property)
    · intro p
      have he0 := extend_multiplicity (code0 g) w.1 (.inr p)
      have he1 := extend_multiplicity (code1 g) w.2 (.inr p)
      change multiplicity (extend (code0 g) w.1) (some p.val) = multiplicity w.1 (some (.inr p)) at he0
      change multiplicity (extend (code1 g) w.2) (some p.val) = multiplicity w.2 (some (.inr p)) at he1
      have hp := hn p
      change multiplicity (extend (code0 g) w.1) (some p.val)+
        multiplicity (extend (code1 g) w.2) (some p.val) = unboundCounts g p at hp
      rw [he0,he1] at hp
      exact hp
  · rintro ⟨⟨h0,h1⟩,hn⟩
    refine ⟨?_,?_⟩
    · intro c
      exact ⟨bishop0_count g w.1 h0 c,bishop1_count g w.2 h1 c,
        kirin0_count g w.1 c,kirin1_count g w.2 h1 c⟩
    · intro p
      have he0 := extend_multiplicity (code0 g) w.1 (.inr p)
      have he1 := extend_multiplicity (code1 g) w.2 (.inr p)
      change multiplicity (extend (code0 g) w.1) (some p.val) = multiplicity w.1 (some (.inr p)) at he0
      change multiplicity (extend (code1 g) w.2) (some p.val) = multiplicity w.2 (some (.inr p)) at he1
      change multiplicity (extend (code0 g) w.1) (some p.val)+
        multiplicity (extend (code1 g) w.2) (some p.val) = unboundCounts g p
      rw [he0,he1]
      exact hn p

theorem represented_supported0 (g : Config r s) (w0 : S0 → Option Piece) (w1 : S1 → Option Piece)
    (h : Represents g (wordCounts w0) (wordCounts w1)) : Supported (code0 g) w0 := by
  have hc := (CanonicalAlphabet.represents_iff g _ _).mp h
  apply (supported_iff_zero _ _).mpr
  rintro ⟨c,p⟩ hout
  by_cases hb : p = .native .bishop
  · subst p
    have hne : (g.bishop c).val.1 ≠ 1 := by
      intro he; exact hout ((code0_range g _).mpr (.inr ⟨rfl,he⟩))
    have hle := ((CanonicalGroups.bishopStates_iff _ _ _).mp (g.bishop c).property).1
    change (g.bishop c).val.1 ≤ 1 at hle
    have he := (hc.1 c).1
    change multiplicity w0 (some (c,.native .bishop)) = (g.bishop c).val.1 at he
    omega
  · by_cases hk : p = .native .kirin
    · subst p; exact (hc.1 c).2.2.1
    · exact False.elim (hout ((code0_range g _).mpr (.inl ⟨hb,hk⟩)))

theorem represented_supported1 (g : Config r s) (w0 : S0 → Option Piece) (w1 : S1 → Option Piece)
    (h : Represents g (wordCounts w0) (wordCounts w1)) : Supported (code1 g) w1 := by
  have hc := (CanonicalAlphabet.represents_iff g _ _).mp h
  apply (supported_iff_zero _ _).mpr
  rintro ⟨c,p⟩ hout
  by_cases hb : p = .native .bishop
  · subst p
    have hne : (g.bishop c).val.2.1 ≠ 1 := by
      intro he; exact hout ((code1_range g _).mpr (.inr (.inl ⟨rfl,he⟩)))
    have hle := ((CanonicalGroups.bishopStates_iff _ _ _).mp (g.bishop c).property).2.1
    change (g.bishop c).val.2.1 ≤ 1 at hle
    have he := (hc.1 c).2.1
    change multiplicity w1 (some (c,.native .bishop)) = (g.bishop c).val.2.1 at he
    omega
  · by_cases hk : p = .native .kirin
    · subst p
      have hne : (g.kirin c).val.1 ≠ 1 := by
        intro he; exact hout ((code1_range g _).mpr (.inr (.inr ⟨rfl,he⟩)))
      have hle := ((CanonicalGroups.jumperStates_iff _ _).mp (g.kirin c).property).1
      change (g.kirin c).val.1 ≤ 1 at hle
      have he := (hc.1 c).2.2.2
      change multiplicity w1 (some (c,.native .kirin)) = (g.kirin c).val.1 at he
      omega
    · exact False.elim (hout ((code1_range g _).mpr (.inl ⟨hb,hk⟩)))

/-- Every actual word in this canonical profile fibre has a unique supported
encoding; no bishop/kirin placements are lost when changing alphabets. -/
noncomputable def fibreEquivalence (g : Config r s) :
    {w : Words (S0 := S0) (S1 := S1) g //
      TwoClassEGF.GoodPair w ∧ TwoClassEGF.Counts (unboundCounts g) w} ≃
    {w : (S0 → Option Piece) × (S1 → Option Piece) // Represents g (wordCounts w.1) (wordCounts w.2)} where
  toFun w := ⟨(extend (code0 g) w.val.1,extend (code1 g) w.val.2),(represents_words g w.val).mpr w.property⟩
  invFun w := by
    let h0 := represented_supported0 g w.val.1 w.val.2 w.property
    let h1 := represented_supported1 g w.val.1 w.val.2 w.property
    let v : Words (S0 := S0) (S1 := S1) g := (restrict (code0 g) w.val.1 h0,restrict (code1 g) w.val.2 h1)
    refine ⟨v,(represents_words g v).mp ?_⟩
    dsimp only [v]
    rw [extend_restrict,extend_restrict]
    exact w.property
  left_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · exact restrict_extend _ _ _
    · exact restrict_extend _ _ _
  right_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · exact extend_restrict _ _ _
    · exact extend_restrict _ _ _

/-- Concrete canonical profile fibre = bound falling factors times the
unrestricted EGF weight. All word/profile/identity premises are discharged. -/
theorem fibre_egf (g : Config r s) :
    (Fintype.card {w : (S0 → Option Piece) × (S1 → Option Piece) //
      Represents g (wordCounts w.1) (wordCounts w.2)} : ℚ) =
      ((Fintype.card S0).descFactorial (Fintype.card (Bound0 g)) : ℚ)*
      ((Fintype.card S1).descFactorial (Fintype.card (Bound1 g)) : ℚ)*
      (((Fintype.card S0-Fintype.card (Bound0 g))+(Fintype.card S1-Fintype.card (Bound1 g))).descFactorial
        (∑ p, unboundCounts g p) : ℚ)*EGFArithmetic.inverseFactorials (unboundCounts g) := by
  rw [← Fintype.card_congr (fibreEquivalence g),TwoClassEGF.count_egf]

end ChuShogi.CanonicalWordProfiles
