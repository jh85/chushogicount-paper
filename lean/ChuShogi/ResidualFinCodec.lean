import ChuShogi.CanonicalUnrestrictedCodec
import ChuShogi.BoundPlacements

/-! Explicit finite ordering of squares left after distinct bound placements.
This replaces a choice of equal-cardinality finite types by a computed filtered
square list, connected to the existing independent residual-word predicate. -/
namespace ChuShogi.ResidualFinCodec
open BoundPlacements CanonicalAlphabet UnrestrictedWords

instance rangeDecidable (e : Fin k ↪ Fin n) (s : Fin n) : Decidable (s ∈ Set.range e) :=
  inferInstanceAs (Decidable (∃ i : Fin k, e i=s))

instance residualDecidableEq (e : Fin k ↪ Fin n) : DecidableEq (Residual e) :=
  inferInstanceAs (DecidableEq {s : Fin n // s ∉ Set.range e})

def positions (e : Fin k ↪ Fin n) : List (Residual e) :=
  FiniteListEquivalence.subtypeEntries (List.finRange n) (fun s => s ∉ Set.range e)

theorem positions_nodup (e : Fin k ↪ Fin n) : (positions e).Nodup :=
  FiniteListEquivalence.subtypeEntries_nodup _ (List.nodup_finRange n) _

theorem positions_complete (e : Fin k ↪ Fin n) (s : Residual e) : s ∈ positions e :=
  FiniteListEquivalence.subtypeEntries_complete _ (fun _ => List.mem_finRange _) _ s

def listEquivalence (e : Fin k ↪ Fin n) : Fin (positions e).length ≃ Residual e :=
  FiniteListEquivalence.equivalence (positions e) (positions_nodup e) (positions_complete e)

theorem positions_length (e : Fin k ↪ Fin n) : (positions e).length = n-k := by
  have h := Fintype.card_congr (listEquivalence e)
  simpa only [Fintype.card_fin,residual_card] using h

def equivalence (e : Fin k ↪ Fin n) : Fin (n-k) ≃ Residual e :=
  (finCongr (positions_length e).symm).trans (listEquivalence e)

def functionEquivalence (e : Fin k ↪ Fin n) (A : Type) : (Fin (n-k) → A) ≃ (Residual e → A) where
  toFun w s := w ((equivalence e).symm s)
  invFun w i := w (equivalence e i)
  left_inv w := by funext i; simp
  right_inv w := by funext s; simp

theorem multiplicity_domain {S T A : Type} [Fintype S] [Fintype T] [DecidableEq A]
    (e : S ≃ T) (w : S → A) (a : A) :
    MultinomialPlacements.multiplicity (fun t => w (e.symm t)) a =
      MultinomialPlacements.multiplicity w a := by
  classical
  apply Fintype.card_congr
  exact {
    toFun t := ⟨e.symm t.val,t.property⟩
    invFun s := ⟨e s.val,by simpa using s.property⟩
    left_inv t := Subtype.ext (e.apply_symm_apply t.val)
    right_inv s := Subtype.ext (e.symm_apply_apply s.val) }

def wordEquivalence (e : Fin k ↪ Fin n) (counts : Unbound → Nat) :
    {w : Fin (n-k) → Option Unbound // SomeCounts counts w} ≃
      {w : Residual e → Option Unbound // SomeCounts counts w} :=
  Equiv.subtypeEquiv (functionEquivalence e (Option Unbound)) (fun w => by
    change SomeCounts counts w ↔ SomeCounts counts (fun s => w ((equivalence e).symm s))
    simp only [SomeCounts,multiplicity_domain])

def canonicalEquivalence (e : Fin k ↪ Fin n) (counts : Unbound → Nat) :
    Fin (CanonicalUnrestrictedCodec.size (n-k) counts) ≃
      {w : Residual e → Option Unbound // SomeCounts counts w} :=
  (CanonicalUnrestrictedCodec.equivalence (n-k) counts).trans (wordEquivalence e counts)

end ChuShogi.ResidualFinCodec
