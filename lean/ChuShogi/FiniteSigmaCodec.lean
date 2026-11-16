import ChuShogi.FiniteListEquivalence

/-! Executable dependent-interval transports. Keeping these generic also keeps
elaboration from unfolding enormous independent finite predicates. -/
namespace ChuShogi.FiniteSigmaCodec

def equivalence {A : Type} (P Q : A → Prop) (hp : ∀ a, P a ↔ Q a)
    (u v : A → Nat) (hn : ∀ a, P a → u a=v a) :
    (Σ a : {a // P a}, Fin (u a.val)) ≃ (Σ a : {a // Q a}, Fin (v a.val)) where
  toFun p := ⟨⟨p.1.val,(hp p.1.val).mp p.1.property⟩,⟨p.2.val,by rw [← hn p.1.val p.1.property]; exact p.2.isLt⟩⟩
  invFun p := ⟨⟨p.1.val,(hp p.1.val).mpr p.1.property⟩,⟨p.2.val,by rw [hn p.1.val ((hp p.1.val).mpr p.1.property)]; exact p.2.isLt⟩⟩
  left_inv p := by apply Sigma.ext rfl; apply heq_of_eq; apply Fin.ext; rfl
  right_inv p := by apply Sigma.ext rfl; apply heq_of_eq; apply Fin.ext; rfl

end ChuShogi.FiniteSigmaCodec
