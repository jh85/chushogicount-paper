import ChuShogi.StructuralCount
import ChuShogi.MathSampling

/-! Whole-Board reference indexing and conditional uniform sampling. This
mathematical finite-list ranker is not the production Python branch ranker and
is not an efficient executable numerical implementation. No RNG is assumed correct. -/
namespace ChuShogi.WholeBoardIndexing
set_option maxRecDepth 8192
open Specification StructuralDecomposition StructuralCount FiniteBoards

/-- Proof-carrying finite enumeration. Keeping this package opaque prevents the
kernel from expanding the astronomically large symbolic Board universe during
index-cast conversion. Its constructor and every field are checked normally. -/
structure CertifiedEnumeration (r : Bool) where
  items : List {b : Board // Stratum r b}
  nodup : items.Nodup
  complete : ∀ b, b ∈ items
  length : items.length = structuralCount r

noncomputable opaque enumerationData (r : Bool) : CertifiedEnumeration r :=
  ⟨subtypeEnum allBoards (Stratum r),subtypeEnum_nodup _ universe_nodup _,
   subtypeEnum_complete allBoards universe_complete _,(structural_count r).symm⟩

noncomputable def enumeration (r : Bool) : List {b : Board // Stratum r b} := (enumerationData r).items

theorem enumeration_nodup (r : Bool) : (enumeration r).Nodup := (enumerationData r).nodup

theorem enumeration_complete (r : Bool) (b : {b : Board // Stratum r b}) : b ∈ enumeration r :=
  (enumerationData r).complete b

theorem enumeration_length (r : Bool) : (enumeration r).length = structuralCount r := (enumerationData r).length

noncomputable def listEquivalence (r : Bool) :
    Fin (enumeration r).length ≃ {b : Board // Stratum r b} := by
  classical
  exact {
    toFun := Indexing.unrank (enumeration r)
    invFun := fun b => Indexing.rank (enumeration r) b (enumeration_complete r b)
    left_inv := Indexing.rank_unrank _ (enumeration_nodup r)
    right_inv := fun b => Indexing.unrank_rank _ b _ }

noncomputable def equivalence (r : Bool) : Fin (structuralCount r) ≃ {b : Board // Stratum r b} :=
  (finCongr (enumeration_length r).symm).trans (listEquivalence r)

noncomputable def unrank (r : Bool) (i : Fin (structuralCount r)) : {b : Board // Stratum r b} := equivalence r i

noncomputable def rank (r : Bool) (b : {b : Board // Stratum r b}) : Fin (structuralCount r) := (equivalence r).symm b

theorem unrank_rank (r : Bool) (b : {b : Board // Stratum r b}) : unrank r (rank r b) = b :=
  (equivalence r).apply_symm_apply b

theorem rank_unrank (r : Bool) (i : Fin (structuralCount r)) : rank r (unrank r i) = i :=
  (equivalence r).symm_apply_apply i

/-- A genuinely uniform input distribution yields a uniform canonical Board.
The input is an actual PMF, so no separate positivity/nonempty assumption or
correctness claim about a concrete random-number generator is needed. -/
theorem uniform_input (r : Bool) (p : PMF (Fin (structuralCount r)))
    (h : ∀ i, p i = (structuralCount r : ENNReal)⁻¹)
    (b : {b : Board // Stratum r b}) :
    (p.map (unrank r)) b = (structuralCount r : ENNReal)⁻¹ := by
  exact MathSampling.uniform_equiv (equivalence r) p _ h b

end ChuShogi.WholeBoardIndexing
