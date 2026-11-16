import ChuShogi.FiniteLookup
import ChuShogi.AlphabetRestriction

/-! Computable inverse of an injectively encoded finite alphabet. The searched
list is proved complete; supported input symbols cannot be silently omitted. -/
namespace ChuShogi.ComputedAlphabetRestriction
open AlphabetRestriction
variable {A B S : Type} [DecidableEq B]

def restrict (e : A ↪ B) (xs : List A) (w : S → Option B) (s : S) : Option A :=
  (w s).bind fun b => xs.find? (fun a => decide (e a=b))

theorem extend_restrict (e : A ↪ B) (xs : List A) (hc : ∀ a, a ∈ xs)
    (w : S → Option B) (hs : Supported e w) :
    extend e (restrict e xs w)=w := by
  funext s
  cases hw : w s with
  | none => simp [restrict,extend,hw]
  | some b =>
    cases hh : xs.find? (fun a => decide (e a=b)) with
    | none =>
      obtain ⟨a,ha⟩ := hs s b hw
      have hnone := (List.find?_eq_none.mp hh) a (hc a)
      simp [ha] at hnone
    | some a =>
      have haBool : decide (e a=b)=true := List.find?_some (p := fun z => decide (e z=b)) (a := a) hh
      have ha : e a=b := of_decide_eq_true haBool
      simp only [extend,restrict,hw,Option.bind_some,hh,Option.map_some,ha]

theorem restrict_eq (e : A ↪ B) (xs : List A) (hc : ∀ a, a ∈ xs)
    (w : S → Option B) (hs : Supported e w) :
    restrict e xs w = AlphabetRestriction.restrict e w hs := by
  apply AlphabetRestriction.extend_injective e
  rw [extend_restrict e xs hc w hs,AlphabetRestriction.extend_restrict e w hs]

theorem restrict_extend (e : A ↪ B) (xs : List A) (hc : ∀ a, a ∈ xs) (w : S → Option A) :
    restrict e xs (extend e w)=w := by
  rw [restrict_eq e xs hc _ (extend_supported e w)]
  exact AlphabetRestriction.restrict_extend e w _

def equivalence (e : A ↪ B) (xs : List A) (hc : ∀ a, a ∈ xs) :
    (S → Option A) ≃ {w : S → Option B // Supported e w} where
  toFun w := ⟨extend e w,extend_supported e w⟩
  invFun w := restrict e xs w.val
  left_inv w := restrict_extend e xs hc w
  right_inv w := Subtype.ext (extend_restrict e xs hc w.val w.property)

end ChuShogi.ComputedAlphabetRestriction
