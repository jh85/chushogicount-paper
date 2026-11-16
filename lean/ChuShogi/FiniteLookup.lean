import ChuShogi.FiniteListEquivalence

/-! Computable witness lookup in an explicitly searched finite list. -/
namespace ChuShogi.FiniteLookup

def findValue (xs : List A) (p : A → Bool) (h : ∃ a ∈ xs, p a=true) : {a // p a=true} :=
  let found := xs.find? p
  have hs : found.isSome=true := List.find?_isSome.mpr h
  ⟨found.get hs,List.find?_some (Option.some_get hs).symm⟩

theorem findValue_unique (xs : List A) (p : A → Bool) (h : ∃ a ∈ xs, p a=true)
    (a : A) (_ha : p a=true) (hu : ∀ b, p b=true → b=a) : (findValue xs p h).val=a :=
  hu _ (findValue xs p h).property

end ChuShogi.FiniteLookup
