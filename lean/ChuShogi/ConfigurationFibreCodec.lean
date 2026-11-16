import ChuShogi.ComputedProfileFibre
import ChuShogi.BoundLabelRelabelling
import ChuShogi.ConfigurationSum

/-! Executable canonical configuration-fibre codec, with no remaining label,
class-placement, unrestricted-word or promotion-origin multiplicity premises.
Selecting the configuration itself remains a separate weighted branch step.
-/
namespace ChuShogi.ConfigurationFibreCodec
open Specification GroupConfigurations CanonicalAlphabet CanonicalBoundLabels CanonicalWordProfiles

def size (g : Config r s) (n0 n1 : Nat) : Nat :=
  TwoClassCanonicalCodec.size (number0 g) (number1 g) n0 n1 (unboundCounts g)

def equivalence (g : Config r s) (n0 n1 : Nat) : Fin (size g n0 n1) ≃
    {w : (Fin n0 → Option Piece) × (Fin n1 → Option Piece) // Represents g (wordCounts w.1) (wordCounts w.2)} :=
  (TwoClassCanonicalCodec.equivalence (number0 g) (number1 g) n0 n1 (unboundCounts g)).trans
    ((BoundLabelRelabelling.equivalence (equivalence0 g) (equivalence1 g) n0 n1 (unboundCounts g)).trans
      (ComputedProfileFibre.equivalence g))

def unrank (g : Config r s) (n0 n1 : Nat) := (equivalence g n0 n1).toFun
def rank (g : Config r s) (n0 n1 : Nat) := (equivalence g n0 n1).invFun

theorem rank_unrank (g : Config r s) (n0 n1 : Nat) (i : Fin (size g n0 n1)) :
    rank g n0 n1 (unrank g n0 n1 i)=i := (equivalence g n0 n1).symm_apply_apply i

theorem unrank_rank (g : Config r s) (n0 n1 : Nat)
    (w : {w : (Fin n0 → Option Piece) × (Fin n1 → Option Piece) // Represents g (wordCounts w.1) (wordCounts w.2)}) :
    unrank g n0 n1 (rank g n0 n1 w)=w := (equivalence g n0 n1).apply_symm_apply w

theorem size_term (g : Config r s) (n0 n1 : Nat) :
    (size g n0 n1 : ℚ) = ConfigurationSum.term n0 n1 g := by
  rw [size,TwoClassCanonicalCodec.size_egf]
  unfold ConfigurationSum.term
  rw [card0,card1]
  rw [show CanonicalUnrestrictedCodec.total (unboundCounts g) = ∑ p, unboundCounts g p from
    (UnboundInventory.sum_entries (unboundCounts g)).symm]

theorem uniform_input (g : Config r s) (n0 n1 : Nat) (p : PMF (Fin (size g n0 n1)))
    (h : ∀ i, p i = (size g n0 n1 : ENNReal)⁻¹)
    (w : {w : (Fin n0 → Option Piece) × (Fin n1 → Option Piece) // Represents g (wordCounts w.1) (wordCounts w.2)}) :
    (p.map (unrank g n0 n1)) w = (size g n0 n1 : ENNReal)⁻¹ :=
  MathSampling.uniform_equiv (equivalence g n0 n1) p _ h w

end ChuShogi.ConfigurationFibreCodec
