import ChuShogi.BoundCanonicalCodec
import ChuShogi.JointResidualCodec

/-! Complete executable two-class placement codec for a fixed canonical count
configuration. All unrestricted class splits are included exactly once. -/
namespace ChuShogi.TwoClassCanonicalCodec
open CanonicalAlphabet BoundPlacements TwoClassEGF

abbrev Words (k0 k1 n0 n1 : Nat) :=
  (Fin n0 → Option (Fin k0 ⊕ Unbound)) × (Fin n1 → Option (Fin k1 ⊕ Unbound))
abbrev Embeddings (k0 k1 n0 n1 : Nat) := (Fin k0 ↪ Fin n0) × (Fin k1 ↪ Fin n1)
abbrev ResidualWords (e : Embeddings k0 k1 n0 n1) :=
  (Residual e.1 → Option Unbound) × (Residual e.2 → Option Unbound)

def size (k0 k1 n0 n1 : Nat) (counts : Unbound → Nat) : Nat :=
  (n0.descFactorial k0*n1.descFactorial k1)*
    CanonicalUnrestrictedCodec.size ((n0-k0)+(n1-k1)) counts

def baseEquivalence :
    (Σ e : Embeddings k0 k1 n0 n1, ResidualWords e) ≃
      {f : Words k0 k1 n0 n1 // GoodPair f} := by
  let split : (Σ e : Embeddings k0 k1 n0 n1, ResidualWords e) ≃
      (Σ e0 : Fin k0 ↪ Fin n0, Residual e0 → Option Unbound) ×
        (Σ e1 : Fin k1 ↪ Fin n1, Residual e1 → Option Unbound) := {
    toFun p := (⟨p.1.1,p.2.1⟩,⟨p.1.2,p.2.2⟩)
    invFun p := ⟨(p.1.1,p.2.1),(p.1.2,p.2.2)⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  let flat : {f0 : Fin n0 → Option (Fin k0 ⊕ Unbound) // Good f0} ×
      {f1 : Fin n1 → Option (Fin k1 ⊕ Unbound) // Good f1} ≃
      {f : Words k0 k1 n0 n1 // GoodPair f} := {
    toFun f := ⟨(f.1.val,f.2.val),f.1.property,f.2.property⟩
    invFun f := (⟨f.val.1,f.property.1⟩,⟨f.val.2,f.property.2⟩)
    left_inv _ := rfl
    right_inv _ := rfl }
  exact split.trans ((Equiv.prodCongr ComputedBoundWords.equivalence ComputedBoundWords.equivalence).trans flat)

def countedEquivalence (counts : Unbound → Nat) :
    (Σ e : Embeddings k0 k1 n0 n1, {w : ResidualWords e // ResidualCounts counts e w}) ≃
      {f : Words k0 k1 n0 n1 // GoodPair f ∧ Counts counts f} := by
  let split : (Σ e : Embeddings k0 k1 n0 n1, {w : ResidualWords e // ResidualCounts counts e w}) ≃
      {p : Σ e : Embeddings k0 k1 n0 n1, ResidualWords e // ResidualCounts counts p.1 p.2} := {
    toFun p := ⟨⟨p.1,p.2.val⟩,p.2.property⟩
    invFun p := ⟨p.val.1,⟨p.val.2,p.property⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  let ref : {p : Σ e : Embeddings k0 k1 n0 n1, ResidualWords e // ResidualCounts counts p.1 p.2} ≃
      {f : {f : Words k0 k1 n0 n1 // GoodPair f} // Counts counts f.val} :=
    Equiv.subtypeEquiv baseEquivalence (fun p => by
      change ResidualCounts counts p.1 p.2 ↔ Counts counts
        (ComputedBoundWords.assemble p.1.1 p.2.1,ComputedBoundWords.assemble p.1.2 p.2.2)
      rw [ComputedBoundWords.assemble_eq,ComputedBoundWords.assemble_eq]
      simp only [ResidualCounts,Counts,unbound_multiplicity])
  exact split.trans (ref.trans (Equiv.subtypeSubtypeEquivSubtypeInter GoodPair (Counts counts)))

def embeddingEquivalence (k0 k1 n0 n1 : Nat) :
    Fin (n0.descFactorial k0*n1.descFactorial k1) ≃ Embeddings k0 k1 n0 n1 :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (InjectionIndexing.equivalence k0 n0) (InjectionIndexing.equivalence k1 n1))

def coordinateEquivalence (k0 k1 n0 n1 : Nat) (counts : Unbound → Nat) : Fin (size k0 k1 n0 n1 counts) ≃
    (Σ e : Embeddings k0 k1 n0 n1, {w : ResidualWords e // ResidualCounts counts e w}) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodCongr (embeddingEquivalence k0 k1 n0 n1) (Equiv.refl _)).trans
      ((Equiv.sigmaEquivProd _ _).symm.trans
        (Equiv.sigmaCongrRight fun e : Embeddings k0 k1 n0 n1 => JointResidualCodec.equivalence e.1 e.2 counts)))

def equivalence (k0 k1 n0 n1 : Nat) (counts : Unbound → Nat) : Fin (size k0 k1 n0 n1 counts) ≃
    {f : Words k0 k1 n0 n1 // GoodPair f ∧ Counts counts f} :=
  (coordinateEquivalence k0 k1 n0 n1 counts).trans (countedEquivalence counts)

def unrank (k0 k1 n0 n1 : Nat) (counts : Unbound → Nat) := (equivalence k0 k1 n0 n1 counts).toFun
def rank (k0 k1 n0 n1 : Nat) (counts : Unbound → Nat) := (equivalence k0 k1 n0 n1 counts).invFun

theorem rank_unrank (k0 k1 n0 n1 : Nat) (counts : Unbound → Nat) (i : Fin (size k0 k1 n0 n1 counts)) :
    rank k0 k1 n0 n1 counts (unrank k0 k1 n0 n1 counts i)=i :=
  (equivalence k0 k1 n0 n1 counts).symm_apply_apply i

theorem unrank_rank (k0 k1 n0 n1 : Nat) (counts : Unbound → Nat)
    (f : {f : Words k0 k1 n0 n1 // GoodPair f ∧ Counts counts f}) :
    unrank k0 k1 n0 n1 counts (rank k0 k1 n0 n1 counts f)=f :=
  (equivalence k0 k1 n0 n1 counts).apply_symm_apply f

theorem size_egf (k0 k1 n0 n1 : Nat) (counts : Unbound → Nat) :
    (size k0 k1 n0 n1 counts : ℚ) = (n0.descFactorial k0 : ℚ)*(n1.descFactorial k1 : ℚ)*
      (((n0-k0)+(n1-k1)).descFactorial (CanonicalUnrestrictedCodec.total counts) : ℚ)*
      EGFArithmetic.inverseFactorials counts := by
  rw [size,Nat.cast_mul,Nat.cast_mul,CanonicalUnrestrictedCodec.size_egf]
  ring

end ChuShogi.TwoClassCanonicalCodec
