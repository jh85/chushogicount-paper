module
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Fintype.CardEmbedding

@[expose] public section

/-! Kernel-checked factorial identities for canonical placements. Identical
pieces are functions on squares, rather than separately labelled origins. -/
namespace ChuShogi.MultinomialPlacements
open scoped Classical
open Equiv MulAction

variable {S R : Type} [Fintype S] [Fintype R] [DecidableEq S] [DecidableEq R]

noncomputable instance domPermFintype : Fintype (Perm S)ᵈᵐᵃ :=
  Fintype.ofEquiv (Perm S) DomMulAct.mk

noncomputable instance orbitFintype (f : S → R) : Fintype (orbit (Perm S)ᵈᵐᵃ f) :=
  Fintype.ofFinite _

noncomputable instance stabilizerFintype (f : S → R) : Fintype (stabilizer (Perm S)ᵈᵐᵃ f) :=
  Fintype.ofFinite _

/-- Multiplicity of one canonical role, including an empty-square role if used. -/
def multiplicity (f : S → R) (r : R) : Nat := Fintype.card {s // f s = r}

/-- Permuting squares gives factorial-many labelled permutations; each canonical
placement is counted by the factorials of its identical-role multiplicities. -/
theorem orbit_factorial (f : S → R) :
    Fintype.card (orbit (Perm S)ᵈᵐᵃ f) * (∏ r, (multiplicity f r).factorial) =
      (Fintype.card S).factorial := by
  classical
  let e : stabilizer (Perm S)ᵈᵐᵃ f ≃ {g : Perm S // f ∘ g = f} :=
    Equiv.subtypeEquiv DomMulAct.mk.symm (fun _ => DomMulAct.mem_stabilizer_iff)
  have hs : Fintype.card (stabilizer (Perm S)ᵈᵐᵃ f) = ∏ r, (multiplicity f r).factorial :=
    (Fintype.card_congr e).trans (DomMulAct.stabilizer_card f)
  have hg : Fintype.card (Perm S)ᵈᵐᵃ = (Fintype.card S).factorial :=
    (Fintype.card_congr (DomMulAct.mk.symm : (Perm S)ᵈᵐᵃ ≃ Perm S)).trans Fintype.card_perm
  simpa only [hs,hg] using card_orbit_mul_card_stabilizer_eq_card_group (Perm S)ᵈᵐᵃ f

/-- The factorial quotient is an exact integer, not a rounded rational. -/
theorem factorial_divisible (f : S → R) :
    (∏ r, (multiplicity f r).factorial) ∣ (Fintype.card S).factorial := by
  exact ⟨Fintype.card (orbit (Perm S)ᵈᵐᵃ f),by rw [← orbit_factorial f]; exact Nat.mul_comm _ _⟩

theorem orbit_quotient (f : S → R) :
    Fintype.card (orbit (Perm S)ᵈᵐᵃ f) =
      (Fintype.card S).factorial / ∏ r, (multiplicity f r).factorial := by
  have hp : (∏ r, (multiplicity f r).factorial) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun _ _ => Nat.factorial_ne_zero _)
  exact Nat.eq_div_of_mul_eq_left hp (orbit_factorial f)

def SameCounts (f g : S → R) : Prop := ∀ r, multiplicity g r = multiplicity f r

noncomputable instance profileFintype (f : S → R) : Fintype {g // SameCounts f g} := Fintype.ofFinite _

omit [Fintype R] [DecidableEq S] in
theorem multiplicity_comp (f : S → R) (e : Perm S) (r : R) :
    multiplicity (f ∘ e) r = multiplicity f r := by
  classical
  apply Fintype.card_congr
  exact {
    toFun := fun s => ⟨e s.val,s.property⟩
    invFun := fun s => ⟨e.symm s.val,by simpa using s.property⟩
    left_inv := fun s => Subtype.ext (e.symm_apply_apply s.val)
    right_inv := fun s => Subtype.ext (e.apply_symm_apply s.val) }

omit [Fintype R] [DecidableEq S] in
/-- Orbit membership is exactly the independent specification of all role counts. -/
theorem orbit_iff_counts (f g : S → R) : g ∈ orbit (Perm S)ᵈᵐᵃ f ↔ SameCounts f g := by
  classical
  constructor
  · intro h
    obtain ⟨e,rfl⟩ := mem_orbit_iff.mp h
    intro r
    exact multiplicity_comp f (DomMulAct.mk.symm e) r
  · intro h
    let e : S ≃ S := (Equiv.sigmaFiberEquiv f).symm.trans
      ((Equiv.sigmaCongrRight fun r => Fintype.equivOfCardEq (h r).symm).trans
        (Equiv.sigmaFiberEquiv g))
    have he (s : S) : g (e s) = f s := ((Fintype.equivOfCardEq (h (f s)).symm) ⟨s,rfl⟩).property
    apply mem_orbit_iff.mpr
    refine ⟨DomMulAct.mk e.symm,?_⟩
    funext s
    change f (e.symm s) = g s
    have hh := he (e.symm s)
    rw [e.apply_symm_apply] at hh
    exact hh.symm

/-- The factorial quotient counts *all and only* square assignments with the
specified canonical multiplicities, with no labelled-origin overcounting. -/
theorem fixed_counts_quotient (f : S → R) :
    Fintype.card {g // SameCounts f g} =
      (Fintype.card S).factorial / ∏ r, (multiplicity f r).factorial := by
  classical
  have he : {g // SameCounts f g} ≃ orbit (Perm S)ᵈᵐᵃ f :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun g => (orbit_iff_counts f g).symm)
  exact (Fintype.card_congr he).trans (orbit_quotient f)

omit [DecidableEq S] in
theorem sum_multiplicities (f : S → R) : ∑ r, multiplicity f r = Fintype.card S := by
  classical
  calc
    ∑ r, multiplicity f r = Fintype.card (Σ r, {s // f s = r}) := Fintype.card_sigma.symm
    _ = Fintype.card S := Fintype.card_congr (Equiv.sigmaFiberEquiv f)

/-- Multinomial evaluation is derived from the independently specified function set. -/
theorem fixed_counts_multinomial (f : S → R) :
    Fintype.card {g // SameCounts f g} = Nat.multinomial Finset.univ (multiplicity f) := by
  rw [fixed_counts_quotient,Nat.multinomial,sum_multiplicities]

variable {T : Type} [Fintype T] [DecidableEq T]

noncomputable instance pairedProfileFintype (f : S → R) (g : T → R) :
    Fintype {p : (S → R) × (T → R) // SameCounts f p.1 ∧ SameCounts g p.2} := Fintype.ofFinite _

/-- Colour classes have independent square assignments, so their canonical
multinomial placement counts multiply. Empty squares can be included as a role. -/
theorem two_class_multinomial (f : S → R) (g : T → R) :
    Fintype.card {p : (S → R) × (T → R) // SameCounts f p.1 ∧ SameCounts g p.2} =
      Nat.multinomial Finset.univ (multiplicity f) * Nat.multinomial Finset.univ (multiplicity g) := by
  classical
  let e : {p : (S → R) × (T → R) // SameCounts f p.1 ∧ SameCounts g p.2} ≃
      {a // SameCounts f a} × {b // SameCounts g b} := {
    toFun := fun p => (⟨p.val.1,p.property.1⟩,⟨p.val.2,p.property.2⟩)
    invFun := fun p => ⟨(p.1.val,p.2.val),p.1.property,p.2.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Fintype.card_congr e,Fintype.card_prod,fixed_counts_multinomial,fixed_counts_multinomial]

/-- Static multiplicity profiles realized by square assignments; no recurrence
or implementation output is used to specify the profile space. -/
abbrev Profiles := Set.range (multiplicity (S := S) (R := R))

noncomputable instance profilesFintype : Fintype (Profiles (S := S) (R := R)) := Fintype.ofFinite _

noncomputable instance allowedFintype (Allowed : (R → Nat) → Prop) :
    Fintype {g : S → R // Allowed (multiplicity g)} := Fintype.ofFinite _

/-- Summing the derived multinomial count over the admissible multiplicity
profiles counts exactly the independently specified square assignments. -/
theorem allowed_profile_sum (Allowed : (R → Nat) → Prop) :
    Fintype.card {g : S → R // Allowed (multiplicity g)} =
      ∑ p : Profiles (S := S) (R := R), if Allowed p.val then Nat.multinomial Finset.univ p.val else 0 := by
  classical
  let classify : {g : S → R // Allowed (multiplicity g)} → Profiles (S := S) (R := R) :=
    fun g => ⟨multiplicity g.val,⟨g.val,rfl⟩⟩
  calc
    Fintype.card {g : S → R // Allowed (multiplicity g)} =
        ∑ p : Profiles (S := S) (R := R), Fintype.card {w // classify w = p} := by
      rw [← Fintype.card_sigma]
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv classify).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : Allowed p.val
      · rw [ite_eq_left hp]
        let f : S → R := Classical.choose p.property
        have hf : multiplicity f = p.val := Classical.choose_spec p.property
        let e : {w // classify w = p} ≃ {g // SameCounts f g} := {
          toFun := fun w => ⟨w.val.val,by
            have hw : multiplicity w.val.val = p.val := congrArg Subtype.val w.property
            intro r
            exact congrFun (hw.trans hf.symm) r⟩
          invFun := fun g => by
            have hg : multiplicity g.val = p.val := (funext g.property).trans hf
            exact ⟨⟨g.val,by rw [hg]; exact hp⟩,Subtype.ext hg⟩
          left_inv := fun w => by apply Subtype.ext; apply Subtype.ext; rfl
          right_inv := fun g => by apply Subtype.ext; rfl }
        rw [Fintype.card_congr e,fixed_counts_multinomial,hf]
      · rw [ite_eq_right hp]
        have hEmpty : IsEmpty {w // classify w = p} := ⟨fun w => by
          have hw : multiplicity w.val.val = p.val := congrArg Subtype.val w.property
          have hallowed := w.val.property
          rw [hw] at hallowed
          exact hp hallowed⟩
        exact Fintype.card_eq_zero_iff.mpr hEmpty

theorem profile_fiber_card (p : Profiles (S := S) (R := R)) :
    Fintype.card {g : S → R // multiplicity g = p.val} = Nat.multinomial Finset.univ p.val := by
  classical
  let f : S → R := Classical.choose p.property
  have hf : multiplicity f = p.val := Classical.choose_spec p.property
  let e : {g : S → R // multiplicity g = p.val} ≃ {g // SameCounts f g} := {
    toFun := fun g => ⟨g.val,fun r => congrFun (g.property.trans hf.symm) r⟩
    invFun := fun g => ⟨g.val,(funext g.property).trans hf⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Fintype.card_congr e,fixed_counts_multinomial,hf]

/-- Weighted profile aggregation is justified by disjoint finite function fibres. -/
theorem weighted_profile_sum (w : (R → Nat) → Nat) :
    (∑ f : S → R, w (multiplicity f)) =
      ∑ p : Profiles (S := S) (R := R), Nat.multinomial Finset.univ p.val * w p.val := by
  classical
  let classify : (S → R) → Profiles (S := S) (R := R) := fun f => ⟨multiplicity f,⟨f,rfl⟩⟩
  have hc (p : Profiles (S := S) (R := R)) :
      Fintype.card {g // classify g = p} = Nat.multinomial Finset.univ p.val := by
    let e : {g // classify g = p} ≃ {g : S → R // multiplicity g = p.val} :=
      Equiv.subtypeEquiv (Equiv.refl _) (fun g => Subtype.ext_iff)
    exact (Fintype.card_congr e).trans (profile_fiber_card p)
  have he := Fintype.sum_fiberwise' classify (fun p => w p.val)
  simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,hc] using he.symm

/-- Two-class profile sums account for all weighted assignments, including
cross-class material constraints expressed by the weight function. -/
theorem two_class_weighted_sum (w : (R → Nat) → (R → Nat) → Nat) :
    (∑ f : S → R, ∑ g : T → R, w (multiplicity f) (multiplicity g)) =
      ∑ p : Profiles (S := S) (R := R), ∑ q : Profiles (S := T) (R := R),
        Nat.multinomial Finset.univ p.val * Nat.multinomial Finset.univ q.val * w p.val q.val := by
  rw [weighted_profile_sum (S := S) (fun m => ∑ g : T → R, w m (multiplicity g))]
  apply Finset.sum_congr rfl
  intro p _
  rw [weighted_profile_sum (S := T) (fun n => w p.val n),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact (Nat.mul_assoc _ _ _).symm

end ChuShogi.MultinomialPlacements




