import ChuShogi.CanonicalPolynomialFamily
import ChuShogi.CompressedPolynomialSelection
import ChuShogi.PlacementCache

/-! Complete executable canonical completion-word ranker/unranker. Group
selection uses coefficient suffixes; fixed-group placement uses the checked
canonical label and word codecs. The product universe stays symbolic.
-/
namespace ChuShogi.CompletionWordCodec
open Specification ConcreteDP CompletionProfiles GroupCoverage GroupConfigurations CanonicalWordProfiles
open CanonicalPolynomialFamily PolynomialSelectionWeights

def size (r : Bool) (s : Summary) (n0 n1 : Nat) : Nat :=
  total (configuration r s) (CompletionCoefficients.placement n0 n1)

theorem score_size (g : Config r s) (n0 n1 : Nat) :
    score (configuration r s) (CompletionCoefficients.placement n0 n1) g = ConfigurationFibreCodec.size g n0 n1 := by
  unfold score
  rw [contribution]
  generalize ConfigurationFibreCodec.size g n0 n1=n
  simp

theorem size_evaluator (r : Bool) (s : Summary) : size r s (72-s.d0) (72-s.d1)=EvaluatorRefinement.evaluateNat r s :=
  congrArg (fun q : ℚ => q.num.toNat) (CanonicalPolynomialFamily.equivalent r s
    (CompletionCoefficients.placement (72-s.d0) (72-s.d1)))

@[irreducible] def groupEquivalence (r : Bool) (s : Summary) (n0 n1 : Nat) :
    Fin (size r s n0 n1) ≃ Σ g : Config r s, Fin (ConfigurationFibreCodec.size g n0 n1) := by
  let c := PlacementCache.prepare n0 n1
  have hn : NaturalWeights (configuration r s) (PlacementCache.test c) :=
    (PlacementCache.test_correct c).symm ▸ natural r s n0 n1
  let e := CompressedPolynomialSelection.equivalence (configuration r s) (PlacementCache.test c) hn
  exact (CompressedPolynomialSelection.retest _ _ _ (PlacementCache.test_correct c) e).trans
    (Equiv.sigmaCongrRight fun g => finCongr (score_size g n0 n1))

@[irreducible] def equivalence (r : Bool) (s : Summary) (hs : Sized s) (n0 n1 : Nat) : Fin (size r s n0 n1) ≃
    {w : (Fin n0 → Option Piece) × (Fin n1 → Option Piece) // ValidProfile r s (wordCounts w.1) (wordCounts w.2)} :=
  (groupEquivalence r s n0 n1).trans (ComputedConfigurationPartition.fibreEquivalence r s hs n0 n1)

def evaluatorEquivalence (r : Bool) (s : Summary) (hs : Sized s) : Fin (EvaluatorRefinement.evaluateNat r s) ≃
    {w : (Fin (72-s.d0) → Option Piece) × (Fin (72-s.d1) → Option Piece) //
      ValidProfile r s (wordCounts w.1) (wordCounts w.2)} :=
  (finCongr (size_evaluator r s).symm).trans (equivalence r s hs _ _)

def unrank (r : Bool) (s : Summary) (hs : Sized s) (n0 n1 : Nat) := (equivalence r s hs n0 n1).toFun
def rank (r : Bool) (s : Summary) (hs : Sized s) (n0 n1 : Nat) := (equivalence r s hs n0 n1).invFun

theorem rank_unrank (r : Bool) (s : Summary) (hs : Sized s) (n0 n1 : Nat) (i : Fin (size r s n0 n1)) :
    rank r s hs n0 n1 (unrank r s hs n0 n1 i)=i := (equivalence r s hs n0 n1).symm_apply_apply i

theorem unrank_rank (r : Bool) (s : Summary) (hs : Sized s) (n0 n1 : Nat)
    (w : {w : (Fin n0 → Option Piece) × (Fin n1 → Option Piece) // ValidProfile r s (wordCounts w.1) (wordCounts w.2)}) :
    unrank r s hs n0 n1 (rank r s hs n0 n1 w)=w := (equivalence r s hs n0 n1).apply_symm_apply w

theorem uniform_input (r : Bool) (s : Summary) (hs : Sized s) (n0 n1 : Nat)
    (p : PMF (Fin (size r s n0 n1))) (h : ∀ i, p i=(size r s n0 n1 : ENNReal)⁻¹)
    (w : {w : (Fin n0 → Option Piece) × (Fin n1 → Option Piece) // ValidProfile r s (wordCounts w.1) (wordCounts w.2)}) :
    (p.map (unrank r s hs n0 n1)) w=(size r s n0 n1 : ENNReal)⁻¹ :=
  MathSampling.uniform_equiv (equivalence r s hs n0 n1) p _ h w

end ChuShogi.CompletionWordCodec
