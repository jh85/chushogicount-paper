import ChuShogi.CompletionCoefficients

/-! A small explicit canonical role inventory. Its 68 unrestricted coloured
roles include the eight forbidden unpromoted confined roles with zero count.
This finite inventory is independent of Board and configuration enumeration.
-/
namespace ChuShogi.UnboundInventory
open Specification Promotion CompletionProfiles GroupConfigurations CanonicalAlphabet
open EGFConvolution ConfigurationFactors CompletionCoefficients
open scoped Classical

def roles : List Role :=
  [.native .king,.native .elephant] ++
    GroupCoverage.ordinary.flatMap (fun k => [.native k.base,.promoted k]) ++
    [.promoted .bishop,.native .lion,.native .phoenix,.native .freeKing,
     .promoted .pawn,.promoted .lance,.promoted .chariot,.promoted .goBetween,
     .native .pawn,.native .lance,.native .chariot,.native .goBetween]

theorem roles_iff (p : Role) : p ∈ roles ↔ p ≠ .native .bishop ∧ p ≠ .native .kirin := by
  cases p with
  | native b => cases b <;> decide
  | promoted k => cases k <;> decide

def entries : List Unbound := [Colour.black,Colour.white].flatMap fun (c : Colour) =>
  roles.attach.map fun (p : {p : Role // p ∈ roles}) =>
    ⟨(c,p.val),by exact (roles_iff p.val).mp p.property⟩

set_option maxRecDepth 4096 in
theorem entries_nodup : entries.Nodup := by decide

theorem entries_complete (p : Unbound) : p ∈ entries := by
  rcases p with ⟨⟨c,t⟩,hp⟩
  have ht := (roles_iff t).mpr hp
  apply List.mem_flatMap.mpr
  refine ⟨c,by cases c <;> simp,?_⟩
  apply List.mem_map.mpr
  exact ⟨⟨t,ht⟩,by simp,rfl⟩

theorem sum_entries (f : Unbound → Nat) : ∑ p, f p = (entries.map f).sum := by
  have he : entries.toFinset = Finset.univ := Finset.ext (fun p => by simp [entries_complete p])
  rw [← he,List.sum_toFinset f entries_nodup]

theorem prod_entries (f : Unbound → Nat) : ∏ p, f p = (entries.map f).prod := by
  have he : entries.toFinset = Finset.univ := Finset.ext (fun p => by simp [entries_complete p])
  rw [← he,List.prod_toFinset f entries_nodup]

def sideCounts (g : Config r s) (c : Colour) : List Nat :=
  GroupWeights.freeEntries g c ++
    [g.promoted c .pawn,g.promoted c .lance,g.promoted c .chariot,g.promoted c .goBetween,0,0,0,0]

theorem entries_counts (g : Config r s) : entries.map (unboundCounts g) = sideCounts g .black ++ sideCounts g .white := by
  rfl

theorem role_sum (g : Config r s) : ∑ p, unboundCounts g p = (sideCounts g .black).sum+(sideCounts g .white).sum := by
  rw [sum_entries,entries_counts,List.sum_append]

theorem role_prod (g : Config r s) : (∏ p, (unboundCounts g p).factorial) =
    ((sideCounts g .black).map Nat.factorial).prod*((sideCounts g .white).map Nat.factorial).prod := by
  rw [prod_entries]
  have hm : entries.map (fun p => (unboundCounts g p).factorial) =
      (entries.map (unboundCounts g)).map Nat.factorial := (List.map_map ..).symm
  rw [hm,entries_counts,List.map_append,List.prod_append]

theorem tuple_m (xs : List Term) : (tupleDegree xs).m = (xs.map fun x => x.1.m).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [tupleDegree,EGFConvolution.add,List.map_cons,List.sum_cons,ih]

theorem tuple_a0 (xs : List Term) : (tupleDegree xs).a0 = (xs.map fun x => x.1.a0).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [tupleDegree,EGFConvolution.add,List.map_cons,List.sum_cons,ih]

theorem tuple_a1 (xs : List Term) : (tupleDegree xs).a1 = (xs.map fun x => x.1.a1).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [tupleDegree,EGFConvolution.add,List.map_cons,List.sum_cons,ih]

theorem free_entries_part (g : Config r s) (c : Colour) :
    GroupWeights.freeEntries (freePart g) c = GroupWeights.freeEntries g c := rfl

theorem degree_m (g : Config r s) :
    (tupleDegree ((inputs g).map FreeEGF.term)).m = ∑ p, unboundCounts g p := by
  rw [tuple_m,role_sum]
  dsimp only [inputs,FreeCoordinates.inputs,sideCounts]
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,FreeEGF.term]
  rw [GroupWeights.unrestricted_degree,GroupWeights.unrestricted_degree]
  simp only [free_entries_part]
  dsimp only [PromotedCoordinates.promotedInputs,promotedPart,FreeGroupModels.stdInput]
  simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil]
  omega

theorem degree_a0 (g : Config r s) :
    (tupleDegree ((inputs g).map FreeEGF.term)).a0 = Fintype.card (Bound0 g) := by
  rw [tuple_a0,bound0_card]
  dsimp only [inputs,FreeCoordinates.inputs]
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,FreeEGF.term]
  rw [GroupWeights.bound0_degree,GroupWeights.bound0_degree]
  simp [PromotedCoordinates.promotedInputs,promotedPart,FreeGroupModels.stdInput,freePart]

theorem degree_a1 (g : Config r s) :
    (tupleDegree ((inputs g).map FreeEGF.term)).a1 = Fintype.card (Bound1 g) := by
  rw [tuple_a1,bound1_card]
  dsimp only [inputs,FreeCoordinates.inputs]
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,FreeEGF.term]
  rw [GroupWeights.bound1_degree,GroupWeights.bound1_degree]
  simp only [freePart]
  simp [PromotedCoordinates.promotedInputs,promotedPart,FreeGroupModels.stdInput]
  omega

theorem divisor_inventory (g : Config r s) : ((inputs g).map FreeEGF.Input.divisor).prod =
    ∏ p, (unboundCounts g p).factorial := by
  rw [role_prod]
  dsimp only [inputs,FreeCoordinates.inputs]
  simp only [List.map_append,List.prod_append]
  rw [GroupWeights.divisor_product,GroupWeights.divisor_product]
  simp only [free_entries_part]
  dsimp only [PromotedCoordinates.promotedInputs,promotedPart,FreeGroupModels.stdInput,sideCounts]
  simp only [List.map_append,List.prod_append]
  generalize ((GroupWeights.freeEntries g .black).map Nat.factorial).prod = b
  generalize ((GroupWeights.freeEntries g .white).map Nat.factorial).prod = w
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    Nat.factorial_zero,Nat.mul_one]
  ac_rfl

theorem weight_divisor (xs : List FreeEGF.Input) : tupleWeight (xs.map FreeEGF.term) =
    1/(((xs.map FreeEGF.Input.divisor).prod : Nat) : ℚ) := by
  induction xs with
  | nil => simp [tupleWeight]
  | cons x xs ih =>
    simp only [List.map_cons,tupleWeight,List.prod_cons,ih,FreeEGF.term,Nat.cast_mul]
    simp [div_eq_mul_inv,mul_comm]

theorem weight_factorials (g : Config r s) : tupleWeight ((inputs g).map FreeEGF.term) =
    EGFArithmetic.inverseFactorials (unboundCounts g) := by
  rw [weight_divisor,divisor_inventory]
  simp [EGFArithmetic.inverseFactorials,div_eq_mul_inv,Finset.prod_inv_distrib]

end ChuShogi.UnboundInventory
