import ChuShogi.FileBranchSemantics
import ChuShogi.WholeBoardIndexing

/-! Connect the executable file coordinates to independent Boards. Only the
terminal completion enumeration is noncomputable; replacing it by an efficient
residual-word decoder is deliberately a separate implementation obligation. -/
namespace ChuShogi.FileBranchReference
open Specification ConcreteDP FileBranchCoordinates FileBranchSemantics
open StructuralDecomposition SummarySufficiency FiniteBoards

structure CompletionEnumeration (r : Bool) (u : Board) where
  items : List {f : Board // StratumCompletes r u f}
  nodup : items.Nodup
  complete : ∀ f, f ∈ items
  length : items.length=card (StratumCompletes r u)

noncomputable opaque completionData (r : Bool) (u : Board) : CompletionEnumeration r u :=
  ⟨subtypeEnum allBoards (StratumCompletes r u),subtypeEnum_nodup _ universe_nodup _,
    subtypeEnum_complete allBoards universe_complete _,rfl⟩

noncomputable def completionEquivalence (r : Bool) (u : Board) :
    Fin (card (StratumCompletes r u)) ≃ {f : Board // StratumCompletes r u f} := by
  classical
  let d := completionData r u
  let e : Fin d.items.length ≃ {f : Board // StratumCompletes r u f} := {
    toFun := Indexing.unrank d.items
    invFun := fun f => Indexing.rank d.items f (d.complete f)
    left_inv := Indexing.rank_unrank _ d.nodup
    right_inv := fun f => Indexing.unrank_rank _ f _ }
  exact (finCongr d.length.symm).trans e

noncomputable def parts (r : Bool) (x : Code r files zero) : {p : Parts // ValidParts r p} :=
  let f := completionEquivalence r (renderAny (tuple r files zero x)) (completionIndex r x)
  ⟨(tuple r files zero x,f.val),root_tuple_valid r x,f.property⟩

noncomputable def partIndex (r : Bool) (p : {p : Parts // ValidParts r p}) : Nat :=
  ((completionEquivalence r (renderAny p.val.1)).symm ⟨p.val.2,p.property.2⟩).val

theorem partIndex_parts (r : Bool) (x : Code r files zero) :
    partIndex r (parts r x) = (leafIndex r files zero x).val := by
  change ((completionEquivalence r (renderAny (tuple r files zero x))).symm
    (completionEquivalence r (renderAny (tuple r files zero x)) (completionIndex r x))).val = _
  rw [Equiv.symm_apply_apply]
  exact Fin.val_cast (terminal_card r x) (leafIndex r files zero x)

theorem parts_injective (r : Bool) : Function.Injective (parts r) := by
  intro x y he
  apply root_coordinates_injective r x y
  · exact congrArg (fun p => p.val.1) he
  · simpa only [partIndex_parts] using congrArg (partIndex r) he

noncomputable def decode (r : Bool) (x : Code r files zero) : {b : Board // Stratum r b} :=
  (decompositionIso r).forward (parts r x)

theorem decode_injective (r : Bool) : Function.Injective (decode r) := by
  intro x y he
  apply parts_injective r
  have h := congrArg (decompositionIso r).backward he
  simpa only [decode,(decompositionIso r).left_inverse] using h

theorem decode_bijective (r : Bool) : Function.Bijective (decode r) := by
  let := Fintype.ofEquiv (Fin (count r zero files)) (FileBranchCoordinates.equivalence r files zero)
  let := Fintype.ofEquiv (Fin (StructuralCount.structuralCount r)) (WholeBoardIndexing.equivalence r)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨decode_injective r,?_⟩
  rw [Fintype.card_congr (FileBranchCoordinates.equivalence r files zero).symm,
    Fintype.card_congr (WholeBoardIndexing.equivalence r).symm,Fintype.card_fin,Fintype.card_fin]
  exact (root_count r).trans (StructuralCount.structural_count r).symm

noncomputable def equivalence (r : Bool) : Code r files zero ≃ {b : Board // Stratum r b} :=
  Equiv.ofBijective (decode r) (decode_bijective r)

noncomputable def boardEquivalence (r : Bool) : Fin (count r zero files) ≃ {b : Board // Stratum r b} :=
  (FileBranchCoordinates.equivalence r files zero).trans (equivalence r)

theorem uniform_input (r : Bool) (p : PMF (Fin (count r zero files)))
    (h : ∀ i, p i = (count r zero files : ENNReal)⁻¹) (b : {b : Board // Stratum r b}) :
    (p.map (boardEquivalence r)) b = (count r zero files : ENNReal)⁻¹ :=
  MathSampling.uniform_equiv (boardEquivalence r) p _ h b

end ChuShogi.FileBranchReference
