import ChuShogi.HashAggregation

/-! Generic sound memoization. Missing values are computed, so preloading a
partial optimization cache cannot silently omit a mathematical contribution. -/
namespace ChuShogi.ValueCache
variable {V : Type}
abbrev Key := List Nat
abbrev Cache (V : Type) := Std.HashMap Key V
def Sound (u : Key → V) (c : Cache V) : Prop := ∀ k v, c[k]? = some v → v = u k

def get (u : Key → V) (c : Cache V) (k : Key) : V × Cache V :=
  match c[k]? with
  | some v => (v,c)
  | none => let v := u k; (v,c.insert k v)

theorem get_correct (u : Key → V) (c : Cache V) (h : Sound u c) (k : Key) :
    (get u c k).1 = u k ∧ Sound u (get u c k).2 := by
  unfold get
  split
  · rename_i v hv
    exact ⟨h k v hv,h⟩
  · constructor
    · rfl
    · intro q v hv
      rw [Std.HashMap.getElem?_insert] at hv
      by_cases he : k=q
      · subst q; simpa using hv.symm
      · have hb : (k == q) = false := by simp [he]
        simp only [hb,Bool.false_eq_true,ite_false] at hv
        exact h q v hv


def run (u : Key → V) : List Key → Cache V → Cache V
  | [],c => c
  | k::ks,c => run u ks (get u c k).2

theorem run_sound (u : Key → V) (ks : List Key) (c : Cache V) (h : Sound u c) : Sound u (run u ks c) := by
  induction ks generalizing c with
  | nil => exact h
  | cons k ks ih => exact ih _ (get_correct u c h k).2

def prepare (u : Key → V) (ks : List Key) : Cache V := run u ks ∅

theorem prepare_sound (u : Key → V) (ks : List Key) : Sound u (prepare u ks) := by
  apply run_sound
  intro k v h
  simp at h

end ChuShogi.ValueCache
