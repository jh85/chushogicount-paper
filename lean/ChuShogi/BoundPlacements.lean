module
public import ChuShogi.MultinomialPlacements

@[expose] public section

/-! Removing singleton bound roles. The labels here are present canonical
role/class labels, never original pieces. The eventual square-class application
uses this bijection separately in each residual square class. -/
namespace ChuShogi.BoundPlacements
open scoped Classical

variable {X S R : Type}

def Residual (e : X ↪ S) := {s : S // s ∉ Set.range e}

def Good (f : S → Option (X ⊕ R)) : Prop := ∀ x, ∃! s, f s = some (.inl x)

theorem good_iff_counts [Fintype S] [DecidableEq X] [DecidableEq R]
    (f : S → Option (X ⊕ R)) : Good f ↔
      ∀ x, MultinomialPlacements.multiplicity f (some (.inl x)) = 1 := by
  unfold Good
  apply forall_congr'
  intro x
  rw [MultinomialPlacements.multiplicity,Fintype.card_subtype]
  exact Fintype.existsUnique_iff_card_one _

noncomputable def assemble (e : X ↪ S) (w : Residual e → Option R) (s : S) : Option (X ⊕ R) :=
  if h : s ∈ Set.range e then some (.inl (Classical.choose h))
  else (w ⟨s,h⟩).map Sum.inr

theorem assemble_image (e : X ↪ S) (w : Residual e → Option R) (x : X) :
    assemble e w (e x) = some (.inl x) := by
  have h : e x ∈ Set.range e := ⟨x,rfl⟩
  simp only [assemble,dite_eq_left h]
  have he : Classical.choose h = x := e.injective (Classical.choose_spec h)
  rw [he]

theorem assemble_residual (e : X ↪ S) (w : Residual e → Option R) (s : Residual e) :
    assemble e w s.val = (w s).map Sum.inr := by
  simp only [assemble,dite_eq_right s.property]
  rfl

theorem assemble_bound_iff (e : X ↪ S) (w : Residual e → Option R) (s : S) (x : X) :
    assemble e w s = some (.inl x) ↔ s = e x := by
  constructor
  · intro hh
    unfold assemble at hh
    split at hh
    · rename_i h
      have hx : Classical.choose h = x := Sum.inl.inj (Option.some.inj hh)
      exact ((Classical.choose_spec h).symm).trans (congrArg e hx)
    · rename_i h
      cases hw : w ⟨s,h⟩ <;> simp [hw] at hh
  · intro h; subst s; exact assemble_image e w x

theorem assemble_good (e : X ↪ S) (w : Residual e → Option R) : Good (assemble e w) := by
  intro x
  exact ⟨e x,assemble_image e w x,fun s hs => (assemble_bound_iff e w s x).mp hs⟩

noncomputable def embedding (f : S → Option (X ⊕ R)) (h : Good f) : X ↪ S where
  toFun x := Classical.choose (h x)
  inj' := by
    intro x y he
    have hx := (Classical.choose_spec (h x)).1
    have hy := (Classical.choose_spec (h y)).1
    change f (Classical.choose (h x)) = some (.inl x) at hx
    change f (Classical.choose (h y)) = some (.inl y) at hy
    change Classical.choose (h x) = Classical.choose (h y) at he
    rw [he] at hx
    exact Sum.inl.inj (Option.some.inj (hx.symm.trans hy))

theorem embedding_lookup (f : S → Option (X ⊕ R)) (h : Good f) (x : X) :
    f (embedding f h x) = some (.inl x) := (Classical.choose_spec (h x)).1

def residualWord (f : S → Option (X ⊕ R)) (e : X ↪ S) (s : Residual e) : Option R :=
  match f s.val with
  | some (.inr r) => some r
  | _ => none

theorem assemble_extract (f : S → Option (X ⊕ R)) (h : Good f) :
    assemble (embedding f h) (residualWord f (embedding f h)) = f := by
  funext s
  by_cases hs : s ∈ Set.range (embedding f h)
  · obtain ⟨x,rfl⟩ := hs
    rw [assemble_image]
    exact (embedding_lookup f h x).symm
  · rw [assemble_residual _ _ (⟨s,hs⟩ : Residual (embedding f h))]
    cases hv : f s with
    | none => simp [residualWord,hv]
    | some v =>
      cases v with
      | inr r => simp [residualWord,hv]
      | inl x =>
        have he : s = embedding f h x := (Classical.choose_spec (h x)).2 s hv
        exact False.elim (hs ⟨x,he.symm⟩)

/-- Every bound-label word is uniquely an injection of its bound labels plus
a word on the remaining squares. No transitions or placements are omitted. -/
noncomputable def equivalence :
    (Σ e : X ↪ S, Residual e → Option R) ≃ {f : S → Option (X ⊕ R) // Good f} :=
  Equiv.ofBijective (fun p => ⟨assemble p.1 p.2,assemble_good p.1 p.2⟩) (by
    constructor
    · rintro ⟨e,w⟩ ⟨e',w'⟩ hh
      have hf : assemble e w = assemble e' w' := congrArg Subtype.val hh
      have he : e = e' := by
        ext x
        have hx := assemble_image e w x
        rw [hf] at hx
        exact (assemble_bound_iff e' w' (e x) x).mp hx
      subst e'
      have hw : w = w' := by
        funext t
        have ht := congrFun hf t.val
        rw [assemble_residual,assemble_residual] at ht
        cases ha : w t <;> cases hb : w' t <;> simp [ha,hb] at ht ⊢
        exact ht
      cases hw
      rfl
    · intro f
      exact ⟨⟨embedding f.val f.property,residualWord f.val (embedding f.val f.property)⟩,
        Subtype.ext (assemble_extract f.val f.property)⟩)

noncomputable instance residualFintype [Fintype S] (e : X ↪ S) : Fintype (Residual e) := by
  unfold Residual
  exact Fintype.ofFinite _

theorem residual_card [Fintype X] [Fintype S] (e : X ↪ S) :
    Fintype.card (Residual e) = Fintype.card S - Fintype.card X := by
  have he : Fintype.card (Residual e) = Fintype.card {s : S // ¬ s ∈ Set.range e} :=
    Fintype.card_congr (Equiv.refl _)
  rw [he,Fintype.card_subtype_compl,Fintype.card_range e]

theorem unbound_multiplicity [Fintype S] [Fintype X] [Fintype R]
    [DecidableEq X] [DecidableEq R]
    (e : X ↪ S) (w : Residual e → Option R) (r : R) :
    MultinomialPlacements.multiplicity (assemble e w) (some (.inr r)) =
      MultinomialPlacements.multiplicity w (some r) := by
  have hn (s : S) (hs : assemble e w s = some (.inr r)) : s ∉ Set.range e := by
    rintro ⟨x,rfl⟩
    rw [assemble_image] at hs
    cases hs
  have hw (s : S) (hs : assemble e w s = some (.inr r)) :
      w ⟨s,hn s hs⟩ = some r := by
    have hh := (assemble_residual e w (⟨s,hn s hs⟩ : Residual e)).symm.trans hs
    cases hv : w ⟨s,hn s hs⟩ <;> simp [hv] at hh ⊢
    exact hh
  apply Fintype.card_congr
  exact {
    toFun := fun s => ⟨⟨s.val,hn s.val s.property⟩,hw s.val s.property⟩
    invFun := fun t => ⟨t.val.val,by rw [assemble_residual e w t.val,t.property]; rfl⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end ChuShogi.BoundPlacements
