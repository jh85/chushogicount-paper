import ChuShogi.FiniteCountsArray

/-! Finite words stored as arrays, with a bijection to the independent function
specification. Array-valued recursive decoding forces each selected tail once.
-/
namespace ChuShogi.ArrayWords
open WordMultiplicity MultinomialPlacements

structure Data (n : Nat) (counts : Fin a → Nat) where
  values : Array (Fin a)
  size : values.size=n
  valid : multiplicity (fun i : Fin n => values[i.val]'(by rw [size]; exact i.isLt))=counts

variable {a n : Nat} {counts : Fin a → Nat}

@[noinline] def read (d : Data n counts) (i : Fin n) : Fin a := d.values[i.val]'(by rw [d.size]; exact i.isLt)

def forward (d : Data n counts) : Words n counts := ⟨read d,d.valid⟩
def backward (w : Words n counts) : Data n counts :=
  ⟨Array.ofFn w.val,by simp,by simpa using w.property⟩

theorem data_ext (d e : Data n counts) (h : d.values=e.values) : d=e := by cases d; cases e; cases h; rfl

@[irreducible] def equivalence (n : Nat) (counts : Fin a → Nat) : Data n counts ≃ Words n counts where
  toFun := forward
  invFun := backward
  left_inv d := by
    apply data_ext
    apply Array.ext
    · simp [backward,d.size]
    · intro i hi hj
      simp [backward,forward,read]
  right_inv w := by
    apply Subtype.ext
    funext i
    simp [forward,backward,read]

def consEquivalence (n : Nat) (counts : Fin a → Nat) : Data (n+1) counts ≃
    Σ r : {r : Fin a // 0<counts r}, Data n (decrement counts r.val) :=
  (equivalence (n+1) counts).trans ((WordMultiplicity.consEquivalence n counts).trans
    (Equiv.sigmaCongrRight fun r => (equivalence n (decrement counts r.val)).symm))

end ChuShogi.ArrayWords
