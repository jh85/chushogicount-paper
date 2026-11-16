import ChuShogi.HashAggregation

/-! A complete weighted query traversal with a sound, initially empty cache.
Cache misses always compute the query. Cache soundness never substitutes for
coverage: the caller supplies a proved complete query list. -/
namespace ChuShogi.MemoizedSum
abbrev Key := List Nat
abbrev Cache := Std.HashMap Key Nat
def Sound (u : Key → Nat) (c : Cache) : Prop := ∀ k v, c[k]? = some v → v = u k

def get (u : Key → Nat) (c : Cache) (k : Key) : Nat × Cache :=
  match c[k]? with
  | some v => (v,c)
  | none => let v := u k; (v,c.insert k v)

theorem get_correct (u : Key → Nat) (c : Cache) (h : Sound u c) (k : Key) :
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

def run (u : Key → Nat) : List (Key × Nat) → Cache → Nat → Nat × Cache
  | [],c,acc => (acc,c)
  | (k,w)::qs,c,acc =>
    let (v,c') := get u c k
    run u qs c' (acc+w*v)

def reference (u : Key → Nat) (qs : List (Key × Nat)) : Nat :=
  (qs.map fun e => e.2*u e.1).sum

theorem run_correct (u : Key → Nat) (qs : List (Key × Nat)) (c : Cache) (acc : Nat)
    (h : Sound u c) : (run u qs c acc).1 = acc+reference u qs ∧ Sound u (run u qs c acc).2 := by
  induction qs generalizing c acc with
  | nil => simpa [run,reference] using h
  | cons e qs ih =>
    obtain ⟨hv,hc⟩ := get_correct u c h e.1
    have hi := ih (get u c e.1).2 (acc+e.2*(get u c e.1).1) hc
    simpa only [run,reference,List.map_cons,List.sum_cons,hv,Nat.add_assoc] using hi

def evaluate (u : Key → Nat) (qs : List (Key × Nat)) : Nat := (run u qs ∅ 0).1

theorem evaluate_correct (u : Key → Nat) (qs : List (Key × Nat)) : evaluate u qs = reference u qs := by
  have h : Sound u ∅ := by intro k v hv; simp at hv
  simpa [evaluate] using (run_correct u qs ∅ 0 h).1

end ChuShogi.MemoizedSum
