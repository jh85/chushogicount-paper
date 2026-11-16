import ChuShogi.FiniteListEquivalence

/-! A complete finite key list partitions independently specified objects by
an observable. The executable inverse finds that observable in the key list. -/
namespace ChuShogi.FiniteFibrePartition
variable {A S : Type} [DecidableEq S]

abbrev Data (keys : List S) (stat : A → S) (weight : S → Nat) :=
  Σ i : Fin keys.length, {a : A // stat a=keys[i.val]} × Fin (weight keys[i.val])

def forward (keys : List S) (stat : A → S) (weight : S → Nat) (p : Data keys stat weight) :
    Σ a : A, Fin (weight (stat a)) :=
  ⟨p.2.1.val,⟨p.2.2.val,by rw [p.2.1.property]; exact p.2.2.isLt⟩⟩

def backward (keys : List S) (stat : A → S) (weight : S → Nat)
    (hc : ∀ a, stat a∈keys) (p : Σ a : A, Fin (weight (stat a))) : Data keys stat weight :=
  let i := Indexing.rank keys (stat p.1) (hc p.1)
  have he : keys[i.val]=stat p.1 := Indexing.unrank_rank keys _ _
  ⟨i,⟨p.1,he.symm⟩,⟨p.2.val,by rw [he]; exact p.2.isLt⟩⟩

theorem forward_backward (keys : List S) (stat : A → S) (weight : S → Nat) (hc : ∀ a, stat a∈keys)
    (p : Σ a : A, Fin (weight (stat a))) : forward keys stat weight (backward keys stat weight hc p)=p := by
  rcases p with ⟨a,⟨i,hi⟩⟩
  rfl

omit [DecidableEq S] in
theorem forward_injective (keys : List S) (hn : keys.Nodup) (stat : A → S) (weight : S → Nat) :
    Function.Injective (forward keys stat weight) := by
  rintro ⟨i,⟨a,ha⟩,k⟩ ⟨j,⟨b,hb⟩,l⟩ he
  have hab : a=b := congrArg Sigma.fst he
  have hkl : k.val=l.val := congrArg (fun p => p.2.val) he
  have hij : i=j := Indexing.unrank_injective keys hn i j (ha.symm.trans (congrArg stat hab |>.trans hb))
  subst j
  subst b
  have hFin : k=l := Fin.ext hkl
  subst l
  rfl

def equivalence (keys : List S) (hn : keys.Nodup) (stat : A → S) (weight : S → Nat) (hc : ∀ a, stat a∈keys) :
    Data keys stat weight ≃ Σ a : A, Fin (weight (stat a)) where
  toFun := forward keys stat weight
  invFun := backward keys stat weight hc
  left_inv p := forward_injective keys hn stat weight (forward_backward keys stat weight hc (forward keys stat weight p))
  right_inv := forward_backward keys stat weight hc

end ChuShogi.FiniteFibrePartition
