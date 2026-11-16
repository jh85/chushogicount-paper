import ChuShogi.WordMultiplicity

/-! A computed snapshot of a finite multiplicity function. Recursive word
steps retain arrays rather than building a chain of decrement functions. -/
namespace ChuShogi.FiniteCountsArray

structure Data (a : Nat) where
  values : Array Nat
  size : values.size=a

def capture (counts : Fin a → Nat) : Data a := ⟨Array.ofFn counts,by simp⟩

@[noinline] def read (d : Data a) (i : Fin a) : Nat := d.values[i.val]'(by rw [d.size]; exact i.isLt)

theorem read_capture (counts : Fin a → Nat) : read (capture counts)=counts := by
  funext i
  simp [read,capture]

end ChuShogi.FiniteCountsArray
