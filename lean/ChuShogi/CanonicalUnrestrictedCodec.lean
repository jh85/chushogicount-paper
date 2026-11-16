import ChuShogi.FiniteListEquivalence
import ChuShogi.UnboundInventory
import ChuShogi.WordIndexing

/-! Actual canonical unrestricted-role word codec. The explicit alphabet has
68 coloured present roles and the empty-square role. Its cardinality and the
implicit empty multiplicity are discharged, including overfull count vectors.
-/
namespace ChuShogi.CanonicalUnrestrictedCodec
open CanonicalAlphabet MultinomialPlacements UnrestrictedWords

def alphabetEntries : List (Option Unbound) := none::UnboundInventory.entries.map some

theorem alphabet_nodup : alphabetEntries.Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · simp
  · exact UnboundInventory.entries_nodup.map (Option.some_injective _)

theorem alphabet_complete (p : Option Unbound) : p ∈ alphabetEntries := by
  cases p with
  | none => simp [alphabetEntries]
  | some p => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,UnboundInventory.entries_complete p,rfl⟩)

theorem alphabet_length : alphabetEntries.length=69 := by decide

def alphabet : Fin alphabetEntries.length ≃ Option Unbound :=
  FiniteListEquivalence.equivalence alphabetEntries alphabet_nodup alphabet_complete

def total (counts : Unbound → Nat) : Nat := (UnboundInventory.entries.map counts).sum

def fullCounts (n : Nat) (counts : Unbound → Nat) : Option Unbound → Nat
  | none => n-total counts
  | some p => counts p

def indexedCounts (n : Nat) (counts : Unbound → Nat) : Fin alphabetEntries.length → Nat :=
  fun i => fullCounts n counts (alphabet i)

def size (n : Nat) (counts : Unbound → Nat) : Nat := WordMultiplicity.ways n (indexedCounts n counts)

theorem some_full (n : Nat) (counts : Unbound → Nat) (w : Fin n → Option Unbound) :
    SomeCounts counts w ↔ multiplicity w=fullCounts n counts := by
  constructor
  · intro h
    funext p
    cases p with
    | some p => exact h p
    | none =>
      have hs := some_sum w
      simp only [Fintype.card_fin] at hs
      have ht : (∑ p, multiplicity w (some p)) = total counts := by
        unfold total
        rw [← UnboundInventory.sum_entries]
        exact Finset.sum_congr rfl (fun p _ => h p)
      rw [ht] at hs
      change multiplicity w none=n-total counts
      omega
  · intro h p
    exact congrFun h (some p)

theorem multiplicity_relabel {A B : Type} [DecidableEq A] [DecidableEq B]
    (w : Fin n → A) (e : A ≃ B) (b : B) :
    multiplicity (fun i => e (w i)) b = multiplicity w (e.symm b) := by
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl _) (fun _ => e.eq_symm_apply.symm)

def relabelEquivalence (n : Nat) (counts : Unbound → Nat) :
    WordMultiplicity.Words n (indexedCounts n counts) ≃
      {w : Fin n → Option Unbound // SomeCounts counts w} where
  toFun w := ⟨fun i => alphabet (w.val i),by
    apply (some_full n counts _).mpr
    funext p
    rw [multiplicity_relabel]
    have h := congrFun w.property (alphabet.symm p)
    simpa only [indexedCounts,Equiv.apply_symm_apply] using h⟩
  invFun w := ⟨fun i => alphabet.symm (w.val i),by
    funext p
    rw [multiplicity_relabel]
    exact congrFun ((some_full n counts w.val).mp w.property) (alphabet p)⟩
  left_inv w := Subtype.ext (by funext i; exact alphabet.symm_apply_apply (w.val i))
  right_inv w := Subtype.ext (by funext i; exact alphabet.apply_symm_apply (w.val i))

def equivalence (n : Nat) (counts : Unbound → Nat) :
    Fin (size n counts) ≃ {w : Fin n → Option Unbound // SomeCounts counts w} :=
  (WordIndexing.equivalence n (indexedCounts n counts)).trans (relabelEquivalence n counts)

def unrank (n : Nat) (counts : Unbound → Nat) := (equivalence n counts).toFun
def rank (n : Nat) (counts : Unbound → Nat) := (equivalence n counts).invFun

theorem rank_unrank (n : Nat) (counts : Unbound → Nat) (i : Fin (size n counts)) :
    rank n counts (unrank n counts i) = i := (equivalence n counts).symm_apply_apply i

theorem unrank_rank (n : Nat) (counts : Unbound → Nat)
    (w : {w : Fin n → Option Unbound // SomeCounts counts w}) :
    unrank n counts (rank n counts w) = w := (equivalence n counts).apply_symm_apply w

theorem size_egf (n : Nat) (counts : Unbound → Nat) :
    (size n counts : ℚ) = (n.descFactorial (total counts) : ℚ)*EGFArithmetic.inverseFactorials counts := by
  classical
  have hc : size n counts = Fintype.card {w : Fin n → Option Unbound // SomeCounts counts w} := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (equivalence n counts)
  rw [hc,some_counts_egf,Fintype.card_fin]
  rw [show total counts = ∑ p, counts p from (UnboundInventory.sum_entries counts).symm]

end ChuShogi.CanonicalUnrestrictedCodec
