import ChuShogi.ConfigurationFibreCodec

/-! Deterministic recovery of the unique canonical group configuration from
actual class words. This replaces the mathematical partition's choice-based
inverse and is the ranker's canonical-group extraction step. -/
namespace ChuShogi.ComputedConfigurationPartition
open Specification ConcreteDP CompletionProfiles GroupCoverage GroupConfigurations CanonicalWordProfiles

theorem represents_ofGrouped (n0 n1 : Counts) (h : Grouped r s n0 n1) :
    Represents (ofGrouped n0 n1 h) n0 n1 :=
  ⟨counts_ofGrouped n0 n1 h,(fun _ => rfl),(fun _ => rfl),fun c => (h.2.2.2.2.2.1 c).2⟩

variable {S0 S1 : Type} [Fintype S0] [Fintype S1]

def forward (r : Bool) (s : Summary) (hs : Sized s)
    (p : Σ g : Config r s, {w : (S0 → Option Piece) × (S1 → Option Piece) //
      Represents g (wordCounts w.1) (wordCounts w.2)}) :
    {w : (S0 → Option Piece) × (S1 → Option Piece) // ValidProfile r s (wordCounts w.1) (wordCounts w.2)} :=
  ⟨p.2.val,(grouped_iff r s hs _ _).mp (represents_grouped p.1 _ _ p.2.property)⟩

def backward (r : Bool) (s : Summary) (hs : Sized s)
    (w : {w : (S0 → Option Piece) × (S1 → Option Piece) // ValidProfile r s (wordCounts w.1) (wordCounts w.2)}) :
    Σ g : Config r s, {w : (S0 → Option Piece) × (S1 → Option Piece) //
      Represents g (wordCounts w.1) (wordCounts w.2)} :=
  let h := (grouped_iff r s hs _ _).mpr w.property
  ⟨ofGrouped (wordCounts w.val.1) (wordCounts w.val.2) h,⟨w.val,represents_ofGrouped _ _ h⟩⟩

theorem forward_eq (r : Bool) (s : Summary) (hs : Sized s)
    (p : Σ g : Config r s, {w : (S0 → Option Piece) × (S1 → Option Piece) //
      Represents g (wordCounts w.1) (wordCounts w.2)}) :
    forward r s hs p = ConfigurationSum.wordEquivalence r s hs p := rfl

theorem forward_backward (r : Bool) (s : Summary) (hs : Sized s)
    (w : {w : (S0 → Option Piece) × (S1 → Option Piece) // ValidProfile r s (wordCounts w.1) (wordCounts w.2)}) :
    forward r s hs (backward r s hs w)=w := rfl

theorem backward_eq (r : Bool) (s : Summary) (hs : Sized s)
    (w : {w : (S0 → Option Piece) × (S1 → Option Piece) // ValidProfile r s (wordCounts w.1) (wordCounts w.2)}) :
    backward r s hs w = (ConfigurationSum.wordEquivalence r s hs).symm w := by
  apply (ConfigurationSum.wordEquivalence r s hs).injective
  rw [← forward_eq,forward_backward,Equiv.apply_symm_apply]

def equivalence (r : Bool) (s : Summary) (hs : Sized s) :
    (Σ g : Config r s, {w : (S0 → Option Piece) × (S1 → Option Piece) //
      Represents g (wordCounts w.1) (wordCounts w.2)}) ≃
    {w : (S0 → Option Piece) × (S1 → Option Piece) // ValidProfile r s (wordCounts w.1) (wordCounts w.2)} where
  toFun := forward r s hs
  invFun := backward r s hs
  left_inv p := by rw [backward_eq,forward_eq,Equiv.symm_apply_apply]
  right_inv := forward_backward r s hs

def fibreEquivalence (r : Bool) (s : Summary) (hs : Sized s) (n0 n1 : Nat) :
    (Σ g : Config r s, Fin (ConfigurationFibreCodec.size g n0 n1)) ≃
      {w : (Fin n0 → Option Piece) × (Fin n1 → Option Piece) //
        ValidProfile r s (wordCounts w.1) (wordCounts w.2)} :=
  (Equiv.sigmaCongrRight fun g => ConfigurationFibreCodec.equivalence g n0 n1).trans (equivalence r s hs)

end ChuShogi.ComputedConfigurationPartition
