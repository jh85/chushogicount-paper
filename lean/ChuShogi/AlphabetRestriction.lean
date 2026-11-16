module
public import ChuShogi.UnrestrictedWords
public import ChuShogi.BoundPlacements

@[expose] public section

/-! Lossless restriction of square words to an injectively coded alphabet.
Coverage is proved from the absence of symbols outside the code's range. -/
namespace ChuShogi.AlphabetRestriction
open scoped Classical
open MultinomialPlacements

variable {A B S : Type}

def sumEmbedding (e : A ↪ S) (f : B ↪ S) (h : ∀ a b, e a ≠ f b) : A ⊕ B ↪ S where
  toFun := Sum.elim e f
  inj' := by
    intro x y he
    cases x with
    | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (e.injective he)
      | inr b => exact False.elim (h a b he)
    | inr a =>
      cases y with
      | inl b => exact False.elim (h b a he.symm)
      | inr b => exact congrArg Sum.inr (f.injective he)

def Supported (e : A ↪ B) (w : S → Option B) : Prop :=
  ∀ s b, w s = some b → b ∈ Set.range e

def extend (e : A ↪ B) (w : S → Option A) (s : S) : Option B := (w s).map e

theorem extend_supported (e : A ↪ B) (w : S → Option A) : Supported e (extend e w) := by
  intro s b hs
  cases hw : w s with
  | none => simp [extend,hw] at hs
  | some a => exact ⟨a,Option.some.inj (by simpa [extend,hw] using hs)⟩

noncomputable def restrict (e : A ↪ B) (w : S → Option B) (h : Supported e w) (s : S) : Option A :=
  match hs : w s with
  | none => none
  | some b => some (Classical.choose (h s b hs))

theorem extend_restrict (e : A ↪ B) (w : S → Option B) (h : Supported e w) :
    extend e (restrict e w h) = w := by
  funext s
  unfold extend restrict
  split
  · rename_i hw
    rw [hw]
    rfl
  · rename_i b hw
    simp only [Option.map_some]
    exact (congrArg some (Classical.choose_spec (h s b hw))).trans hw.symm

theorem extend_injective (e : A ↪ B) : Function.Injective (extend (S := S) e) := by
  intro w v h
  funext s
  have hh := congrFun h s
  cases hw : w s <;> cases hv : v s <;> simp [extend,hw,hv] at hh ⊢
  exact hh

theorem restrict_extend (e : A ↪ B) (w : S → Option A) (h : Supported e (extend e w)) :
    restrict e (extend e w) h = w := extend_injective e (extend_restrict e _ _)

noncomputable def equivalence (e : A ↪ B) :
    (S → Option A) ≃ {w : S → Option B // Supported e w} where
  toFun w := ⟨extend e w,extend_supported e w⟩
  invFun w := restrict e w.val w.property
  left_inv _w := extend_injective e (extend_restrict e _ _)
  right_inv w := Subtype.ext (extend_restrict e w.val w.property)

theorem extend_multiplicity [Fintype S] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (w : S → Option A) (a : A) :
    multiplicity (extend e w) (some (e a)) = multiplicity w (some a) := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv (Equiv.refl S)
  intro s
  cases hw : w s <;> simp [extend,hw,e.injective.eq_iff]

theorem supported_iff_zero [Fintype S] [DecidableEq B] (e : A ↪ B) (w : S → Option B) :
    Supported e w ↔ ∀ b, b ∉ Set.range e → multiplicity w (some b) = 0 := by
  constructor
  · intro h b hb
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun s => hb (h s.val b s.property)⟩
  · intro h s b hs
    by_contra hb
    have he := h b hb
    have hp : 0 < multiplicity w (some b) := Fintype.card_pos_iff.mpr ⟨⟨s,hs⟩⟩
    omega

theorem bound_symbol_count {X R : Type} [Fintype S] [DecidableEq X] [DecidableEq R] [DecidableEq B]
    (e : X ⊕ R ↪ B) (w : S → Option (X ⊕ R)) (hg : BoundPlacements.Good w)
    (b : B) (n : Nat) (hn : n ≤ 1) (hr : b ∈ Set.range e ↔ n = 1)
    (hu : ∀ r, e (.inr r) ≠ b) : multiplicity (extend e w) (some b) = n := by
  by_cases h1 : n = 1
  · obtain ⟨x,hx⟩ := hr.mpr h1
    cases x with
    | inl x =>
      have hm := extend_multiplicity e w (.inl x)
      rw [hx] at hm
      rw [hm,(BoundPlacements.good_iff_counts w).mp hg x,h1]
    | inr r => exact False.elim (hu r hx)
  · have hout : b ∉ Set.range e := fun hb => h1 (hr.mp hb)
    have hz := (supported_iff_zero e (extend e w)).mp (extend_supported e w) b hout
    omega

end ChuShogi.AlphabetRestriction
