import ChuShogi.CanonicalBoundLabels
import ChuShogi.ComputedAlphabetRestriction
import ChuShogi.CanonicalWordProfiles
import ChuShogi.UnboundInventory

/-! Computable restriction/extension for the actual canonical profile fibres.
Both encoded alphabets have proved complete finite search lists. -/
namespace ChuShogi.ComputedProfileFibre
open Specification Promotion GroupConfigurations CanonicalAlphabet CanonicalBoundLabels
open CanonicalWordProfiles AlphabetRestriction

def labels0 (g : Config r s) : List (Bound0 g ⊕ Unbound) :=
  (List.finRange (number0 g)).map (fun i => .inl (equivalence0 g i)) ++ UnboundInventory.entries.map Sum.inr
def labels1 (g : Config r s) : List (Bound1 g ⊕ Unbound) :=
  (List.finRange (number1 g)).map (fun i => .inl (equivalence1 g i)) ++ UnboundInventory.entries.map Sum.inr

theorem labels0_complete (g : Config r s) (p : Bound0 g ⊕ Unbound) : p ∈ labels0 g := by
  cases p with
  | inl b => exact List.mem_append.mpr (.inl (List.mem_map.mpr
      ⟨(equivalence0 g).symm b,List.mem_finRange _,congrArg Sum.inl ((equivalence0 g).apply_symm_apply b)⟩))
  | inr p => exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨p,UnboundInventory.entries_complete p,rfl⟩))

theorem labels1_complete (g : Config r s) (p : Bound1 g ⊕ Unbound) : p ∈ labels1 g := by
  cases p with
  | inl b => exact List.mem_append.mpr (.inl (List.mem_map.mpr
      ⟨(equivalence1 g).symm b,List.mem_finRange _,congrArg Sum.inl ((equivalence1 g).apply_symm_apply b)⟩))
  | inr p => exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨p,UnboundInventory.entries_complete p,rfl⟩))

variable {S0 S1 : Type} [Fintype S0] [Fintype S1]

def equivalence (g : Config r s) :
    {w : Words (S0 := S0) (S1 := S1) g // TwoClassEGF.GoodPair w ∧ TwoClassEGF.Counts (unboundCounts g) w} ≃
      {w : (S0 → Option Piece) × (S1 → Option Piece) // Represents g (wordCounts w.1) (wordCounts w.2)} where
  toFun w := ⟨(extend (code0 g) w.val.1,extend (code1 g) w.val.2),(represents_words g w.val).mpr w.property⟩
  invFun w := by
    let h0 := represented_supported0 g w.val.1 w.val.2 w.property
    let h1 := represented_supported1 g w.val.1 w.val.2 w.property
    let v : Words (S0 := S0) (S1 := S1) g :=
      (ComputedAlphabetRestriction.restrict (code0 g) (labels0 g) w.val.1,
       ComputedAlphabetRestriction.restrict (code1 g) (labels1 g) w.val.2)
    refine ⟨v,(represents_words g v).mp ?_⟩
    dsimp only [v]
    rw [ComputedAlphabetRestriction.extend_restrict _ _ (labels0_complete g) _ h0,
      ComputedAlphabetRestriction.extend_restrict _ _ (labels1_complete g) _ h1]
    exact w.property
  left_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · exact ComputedAlphabetRestriction.restrict_extend _ _ (labels0_complete g) w.val.1
    · exact ComputedAlphabetRestriction.restrict_extend _ _ (labels1_complete g) w.val.2
  right_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · exact ComputedAlphabetRestriction.extend_restrict _ _ (labels0_complete g) _
        (represented_supported0 g w.val.1 w.val.2 w.property)
    · exact ComputedAlphabetRestriction.extend_restrict _ _ (labels1_complete g) _
        (represented_supported1 g w.val.1 w.val.2 w.property)

end ChuShogi.ComputedProfileFibre
