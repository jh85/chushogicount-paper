import ChuShogi.Indexing
import ChuShogi.WeightedBranches

/-! Executable relabelling of an explicitly complete finite alphabet. -/
namespace ChuShogi.FiniteListEquivalence
variable {A : Type} [DecidableEq A]

def equivalence (xs : List A) (hn : xs.Nodup) (hc : ∀ a, a ∈ xs) : Fin xs.length ≃ A where
  toFun := Indexing.unrank xs
  invFun a := Indexing.rank xs a (hc a)
  left_inv := Indexing.rank_unrank xs hn
  right_inv a := Indexing.unrank_rank xs a (hc a)

def subtypeEntries (xs : List A) (p : A → Prop) [DecidablePred p] : List {a // p a} :=
  (xs.filter fun a => decide (p a)).attach.map fun a =>
    ⟨a.val,by
      have h := a.property
      simp only [List.mem_filter,decide_eq_true_eq] at h
      exact h.2⟩

omit [DecidableEq A] in
theorem subtypeEntries_complete (xs : List A) (hc : ∀ a, a ∈ xs)
    (p : A → Prop) [DecidablePred p] (a : {a // p a}) : a ∈ subtypeEntries xs p := by
  unfold subtypeEntries
  apply List.mem_map.mpr
  have hm : a.val ∈ xs.filter (fun a => decide (p a)) := by simp [hc,a.property]
  exact ⟨⟨a.val,hm⟩,by simp,rfl⟩

omit [DecidableEq A] in
theorem subtypeEntries_nodup (xs : List A) (hn : xs.Nodup)
    (p : A → Prop) [DecidablePred p] : (subtypeEntries xs p).Nodup := by
  rw [subtypeEntries,List.nodup_iff_pairwise_ne,List.pairwise_map]
  have hh : (((xs.filter fun a => decide (p a)).attach).map Subtype.val).Nodup := by
    rw [List.attach_map_subtype_val]
    exact hn.filter _
  change (((xs.filter fun a => decide (p a)).attach).map Subtype.val).Pairwise _ at hh
  rw [List.pairwise_map] at hh
  apply List.Pairwise.imp _ hh
  intro a b hab he
  exact hab (congrArg (fun a : {a // p a} => a.val) he)

end ChuShogi.FiniteListEquivalence
