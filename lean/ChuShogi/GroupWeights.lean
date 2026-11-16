import ChuShogi.FreeEGF

/-! The source term divisors are exactly factorials of present canonical
unrestricted role multiplicities. Bishops/kirins forced onto square classes
are separate singleton labels, not possible origin assignments. -/
namespace ChuShogi.GroupWeights
open Specification Promotion CompletionProfiles CanonicalGroups GroupCoverage GroupConfigurations FreeEGF

def stdInput (g : Config r s) (c : Colour) (k : Separate) : Input :=
  let v := sep g c k
  ⟨⟨v.1+v.2,0,0⟩,v.1.factorial*v.2.factorial⟩

def configInputs (g : Config r s) (c : Colour) : List Input :=
  let ro := (g.royal c).val
  let bi := (g.bishop c).val
  let ki := (g.kirin c).val
  let ph := (g.phoenix c).val
  ⟨⟨ro.1+ro.2,0,0⟩,ro.1.factorial⟩ ::
    ordinary.map (stdInput g c) ++
    [⟨⟨bi.2.2,bi.1,bi.2.1⟩,bi.1.factorial*bi.2.1.factorial*bi.2.2.factorial⟩,
     ⟨⟨ki.2,0,ki.1⟩,ki.2.factorial⟩,
     ⟨⟨ph.1+ph.2,0,0⟩,ph.2.factorial⟩]

/-- One entry per unrestricted canonical role, including zero multiplicities;
the six promoted-confined roles and both promoted pawn roles are handled later. -/
def freeEntries (g : Config r s) (c : Colour) : List Nat :=
  [(g.royal c).val.1,(g.royal c).val.2] ++
    ordinary.flatMap (fun k => [(sep g c k).1,(sep g c k).2]) ++
    [(g.bishop c).val.2.2,(g.kirin c).val.2,(g.phoenix c).val.1,(g.phoenix c).val.2]

theorem singleton_factorials (g : Config r s) (c : Colour) :
    (g.royal c).val.2.factorial = 1 ∧
    (g.bishop c).val.1.factorial = 1 ∧ (g.bishop c).val.2.1.factorial = 1 ∧
    (g.phoenix c).val.1.factorial = 1 := by
  have hr := (royalList_iff r c _ _).mp (g.royal c).property
  have hb := (bishopStates_iff _ _ _).mp (g.bishop c).property
  have hp := (jumperStates_iff _ _).mp (g.phoenix c).property
  exact ⟨Nat.factorial_eq_one.mpr hr.1.1,Nat.factorial_eq_one.mpr hb.1,
    Nat.factorial_eq_one.mpr hb.2.1,Nat.factorial_eq_one.mpr hp.1⟩

theorem standard_divisors (g : Config r s) (c : Colour) (ks : List Separate) :
    ((ks.map (stdInput g c)).map Input.divisor).prod =
      ((ks.flatMap fun k => [(sep g c k).1,(sep g c k).2]).map Nat.factorial).prod := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.map_cons,List.flatMap_cons,List.map_append,List.prod_cons,
      List.prod_append,List.map_nil,List.prod_nil,stdInput]
    rw [ih]
    simp only [Nat.mul_one,Nat.mul_assoc]

theorem standard_degrees (g : Config r s) (c : Colour) (ks : List Separate) :
    ((ks.map (stdInput g c)).map fun i => i.degree.m).sum =
      (ks.flatMap fun k => [(sep g c k).1,(sep g c k).2]).sum := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.map_cons,List.flatMap_cons,List.sum_cons,List.sum_append,
      List.sum_nil,stdInput]
    rw [ih]
    omega

/-- Exact agreement of the canonical reciprocal factorial weight and the source
`Std/Royal/Bound/Jumper` divisor product, including the identity merges. -/
theorem divisor_product (g : Config r s) (c : Colour) :
    ((configInputs g c).map Input.divisor).prod =
      ((freeEntries g c).map Nat.factorial).prod := by
  obtain ⟨hr,hb0,hb1,hp⟩ := singleton_factorials g c
  dsimp only [configInputs,freeEntries]
  simp only [List.map_cons,List.map_append,List.map_nil,List.prod_cons,
    List.prod_append,List.prod_nil]
  rw [standard_divisors g c ordinary,hr,hb0,hb1,hp]
  simp only [Nat.one_mul,Nat.mul_one]

theorem unrestricted_degree (g : Config r s) (c : Colour) :
    ((configInputs g c).map fun i => i.degree.m).sum = (freeEntries g c).sum := by
  dsimp only [configInputs,freeEntries]
  simp only [List.map_cons,List.map_append,List.map_nil,List.sum_cons,List.sum_append,List.sum_nil]
  rw [standard_degrees g c ordinary]
  omega

theorem bound0_degree (g : Config r s) (c : Colour) :
    ((configInputs g c).map fun i => i.degree.a0).sum = (g.bishop c).val.1 := by
  simp [configInputs,ordinary,stdInput]

theorem bound1_degree (g : Config r s) (c : Colour) :
    ((configInputs g c).map fun i => i.degree.a1).sum =
      (g.bishop c).val.2.1 + (g.kirin c).val.1 := by
  simp [configInputs,ordinary,stdInput]

theorem std_input_mem (g : Config r s) (c : Colour) (k : Separate) (h : k ∈ ordinary) :
    stdInput g c k ∈ stdInputs := by
  apply List.mem_map.mpr
  refine ⟨(g.std c k h).val,(g.std c k h).property,?_⟩
  simp only [stdInput,sep,dite_eq_left h]

theorem forall₂_maps (xs : List α) (f : α → β) (g : α → γ) (R : β → γ → Prop)
    (h : ∀ x ∈ xs, R (f x) (g x)) : List.Forall₂ R (xs.map f) (xs.map g) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem forall₂_append {R : α → β → Prop} {a c : List α} {b d : List β}
    (h : List.Forall₂ R a b) (h' : List.Forall₂ R c d) : List.Forall₂ R (a++c) (b++d) := by
  induction h with
  | nil => exact h'
  | cons h _ ih => exact .cons h ih

/-- Each actual canonical coordinate contributes precisely a source term in
the corresponding group, in source order. Term images need not be injective;
equal terms from different role counts must retain their multiplicity. -/
theorem config_inputs_membership (g : Config r s) (c : Colour) :
    List.Forall₂ (fun i xs => i ∈ xs) (configInputs g c) (sideInputs r c) := by
  apply List.Forall₂.cons
  · exact List.mem_map.mpr ⟨(g.royal c).val,(g.royal c).property,rfl⟩
  · apply forall₂_append
    · exact forall₂_maps ordinary _ _ _ (fun k hk => std_input_mem g c k hk)
    · apply List.Forall₂.cons
      · exact List.mem_map.mpr ⟨(g.bishop c).val,(g.bishop c).property,rfl⟩
      · apply List.Forall₂.cons
        · exact List.mem_map.mpr ⟨(g.kirin c).val,(g.kirin c).property,rfl⟩
        · apply List.Forall₂.cons
          · exact List.mem_map.mpr ⟨(g.phoenix c).val,(g.phoenix c).property,rfl⟩
          · exact .nil

end ChuShogi.GroupWeights
