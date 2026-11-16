import ChuShogi.ComputedBoundWords
import ChuShogi.InjectionIndexing

/-! A fully executable codec for one square class: distinct canonical bound
labels plus an exact unrestricted canonical multiset. The independent word
predicate and its EGF formula are the already checked reference definitions. -/
namespace ChuShogi.BoundCanonicalCodec
open CanonicalAlphabet BoundPlacements UnrestrictedWords

def size (k n : Nat) (counts : Unbound → Nat) : Nat :=
  n.descFactorial k*CanonicalUnrestrictedCodec.size (n-k) counts

def countedEquivalence (counts : Unbound → Nat) :
    (Σ e : Fin k ↪ Fin n, {w : Residual e → Option Unbound // SomeCounts counts w}) ≃
      {f : Fin n → Option (Fin k ⊕ Unbound) // BoundWordCounts.Conditions counts f} := by
  let split : (Σ e : Fin k ↪ Fin n, {w : Residual e → Option Unbound // SomeCounts counts w}) ≃
      {p : Σ e : Fin k ↪ Fin n, Residual e → Option Unbound // SomeCounts counts p.2} := {
    toFun p := ⟨⟨p.1,p.2.val⟩,p.2.property⟩
    invFun p := ⟨p.val.1,⟨p.val.2,p.property⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  let ref : {p : Σ e : Fin k ↪ Fin n, Residual e → Option Unbound // SomeCounts counts p.2} ≃
      {f : {f : Fin n → Option (Fin k ⊕ Unbound) // Good f} //
        ∀ r, MultinomialPlacements.multiplicity f.val (some (.inr r))=counts r} :=
    Equiv.subtypeEquiv ComputedBoundWords.equivalence (fun p => by
      change SomeCounts counts p.2 ↔ ∀ r,
        MultinomialPlacements.multiplicity (ComputedBoundWords.assemble p.1 p.2) (some (.inr r))=counts r
      rw [ComputedBoundWords.assemble_eq]
      simp only [SomeCounts,unbound_multiplicity])
  exact split.trans (ref.trans (Equiv.subtypeSubtypeEquivSubtypeInter
    (Good (X := Fin k) (S := Fin n) (R := Unbound))
    (fun f => ∀ r, MultinomialPlacements.multiplicity f (some (.inr r))=counts r)))

def coordinateEquivalence (k n : Nat) (counts : Unbound → Nat) : Fin (size k n counts) ≃
    (Σ e : Fin k ↪ Fin n, {w : Residual e → Option Unbound // SomeCounts counts w}) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodCongr (InjectionIndexing.equivalence k n) (Equiv.refl _)).trans
      ((Equiv.sigmaEquivProd _ _).symm.trans
        (Equiv.sigmaCongrRight fun e => ResidualFinCodec.canonicalEquivalence e counts)))

def equivalence (k n : Nat) (counts : Unbound → Nat) : Fin (size k n counts) ≃
    {f : Fin n → Option (Fin k ⊕ Unbound) // BoundWordCounts.Conditions counts f} :=
  (coordinateEquivalence k n counts).trans (countedEquivalence counts)

def unrank (k n : Nat) (counts : Unbound → Nat) := (equivalence k n counts).toFun
def rank (k n : Nat) (counts : Unbound → Nat) := (equivalence k n counts).invFun

theorem rank_unrank (k n : Nat) (counts : Unbound → Nat) (i : Fin (size k n counts)) :
    rank k n counts (unrank k n counts i) = i := (equivalence k n counts).symm_apply_apply i

theorem unrank_rank (k n : Nat) (counts : Unbound → Nat)
    (w : {f : Fin n → Option (Fin k ⊕ Unbound) // BoundWordCounts.Conditions counts f}) :
    unrank k n counts (rank k n counts w)=w := (equivalence k n counts).apply_symm_apply w

theorem size_egf (k n : Nat) (counts : Unbound → Nat) :
    (size k n counts : ℚ) = (n.descFactorial k : ℚ)*
      ((n-k).descFactorial (CanonicalUnrestrictedCodec.total counts) : ℚ)*
      EGFArithmetic.inverseFactorials counts := by
  rw [size,Nat.cast_mul,CanonicalUnrestrictedCodec.size_egf]
  ring

end ChuShogi.BoundCanonicalCodec
