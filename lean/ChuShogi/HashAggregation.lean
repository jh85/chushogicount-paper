import Std.Data.HashMap.Lemmas
import ChuShogi.AggregationOrder

/-! Hash accumulation with a complete weighted-sum semantics. Standard hash-map
proofs connect every stored key/value to its lookup; a supplied sparse state set
is never assumed complete. This is a numerical-backend refinement prerequisite.
-/
namespace ChuShogi.HashAggregation
open WeightedDP
variable {S : Type} [BEq S] [Hashable S] [LawfulBEq S] [DecidableEq S]

omit [BEq S] [Hashable S] [LawfulBEq S] [DecidableEq S] in
theorem integral_perm (t u : Table S) (h : t.Perm u) (f : S → Nat) : integral t f = integral u f :=
  (h.map (fun (e : S × Nat) => e.2*f e.1)).sum_eq

omit [BEq S] [Hashable S] [LawfulBEq S] in
theorem lookup_cons (e : S × Nat) (t : Table S) (s : S) :
    lookup (e::t) s = e.2*(if e.1=s then 1 else 0)+lookup t s := rfl

omit [Hashable S] in
theorem partition (t : Table S) (s : S) (f : S → Nat) : integral t f =
    lookup t s*f s+integral (t.filter fun e => !(s == e.1)) f := by
  induction t with
  | nil => simp [lookup]
  | cons e t ih =>
    rcases e with ⟨k,v⟩
    by_cases h : k = s
    · subst k
      simp [lookup_cons,ih,Nat.add_mul,Nat.add_assoc]
    · have hn : s ≠ k := Ne.symm h
      simp [lookup_cons,h,hn,ih,Nat.add_left_comm]

omit [DecidableEq S] in
theorem toList_nodup (m : Std.HashMap S Nat) : m.toList.Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  apply m.distinct_keys_toList.imp
  intro a b h he
  cases he
  simp at h

theorem lookup_toList (m : Std.HashMap S Nat) (s : S) : lookup m.toList s = m[s]?.getD 0 := by
  unfold lookup integral
  rw [← List.sum_toFinset _ (toList_nodup m)]
  cases hm : m[s]? with
  | none =>
    simp only [Option.getD_none]
    apply Finset.sum_eq_zero
    intro e he
    have hv := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp (List.mem_toFinset.mp he)
    by_cases hk : e.1=s
    · rw [hk,hm] at hv
      cases hv
    · simp [hk]
  | some v =>
    simp only [Option.getD_some]
    have hs : (s,v) ∈ m.toList.toFinset := List.mem_toFinset.mpr
      (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hm)
    rw [Finset.sum_eq_single (s,v)]
    · simp
    · intro e he hne
      have hv := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp (List.mem_toFinset.mp he)
      by_cases hk : e.1=s
      · rw [hk,hm] at hv
        have hw : v=e.2 := Option.some.inj hv
        exact False.elim (hne (Prod.ext hk hw.symm))
      · simp [hk]
    · exact fun h => False.elim (h hs)

def add (m : Std.HashMap S Nat) (s : S) (w : Nat) : Std.HashMap S Nat := m.insert s (w+m[s]?.getD 0)

theorem integral_add (m : Std.HashMap S Nat) (s : S) (w : Nat) (f : S → Nat) :
    integral (add m s w).toList f = w*f s+integral m.toList f := by
  have hp := Std.HashMap.toList_insert_perm (m := m) (k := s) (v := w+m[s]?.getD 0)
  rw [add,integral_perm _ _ hp,integral_cons]
  rw [partition m.toList s f,lookup_toList,Nat.add_mul,Nat.add_assoc]
  simp
  apply congrArg (fun t => integral t f)
  apply List.filter_congr
  intro e _
  by_cases he : s = e.1
  · rw [he]; simp
  · have hb : (s == e.1) = false := Bool.eq_false_iff.mpr (fun h => he (eq_of_beq h))
    simp [he,hb]

def accumulate (xs : Table S) : Std.HashMap S Nat := xs.foldr (fun e m => add m e.1 e.2) ∅

theorem accumulate_integral (xs : Table S) (f : S → Nat) :
    integral (accumulate xs).toList f = integral xs f := by
  induction xs with
  | nil => simp [accumulate,integral]
  | cons e xs ih =>
    change integral (add (accumulate xs) e.1 e.2).toList f = _
    rw [integral_add,ih,integral_cons]

theorem fold_add_integral (xs : List A) (make : A → S × Nat) (m : Std.HashMap S Nat) (f : S → Nat) :
    integral (xs.foldl (fun m x => add m (make x).1 (make x).2) m).toList f =
      integral m.toList f+(xs.map fun x => (make x).2*f (make x).1).sum := by
  induction xs generalizing m with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons,List.map_cons,List.sum_cons,ih,integral_add]
    omega

/-- Construct the local histogram with hash insertion, then expose a table.
The complete local configuration list is still the source of every entry. -/
def histogram (xs : List A) (feature : A → S) : Table S :=
  (accumulate (xs.map fun x => (feature x,1))).toList

theorem histogram_integral (xs : List A) (feature : A → S) (f : S → Nat) :
    integral (histogram xs feature) f = integral (WeightedDP.histogram xs feature) f := by
  rw [WeightedDP.integral_histogram]
  rw [histogram,accumulate_integral]
  simp [integral,List.map_map,Function.comp_def]

def convolve (merge : S → S → S) (a b : Table S) : Table S :=
  (a.foldl (fun m e => b.foldl (fun m v => add m (merge e.1 v.1) (e.2*v.2)) m) ∅).toList

theorem convolve_integral (merge : S → S → S) (a b : Table S) (f : S → Nat) :
    integral (convolve merge a b) f = integral (WeightedDP.convolve merge a b) f := by
  have inner (e : S × Nat) (m : Std.HashMap S Nat) :
      integral (b.foldl (fun m v => add m (merge e.1 v.1) (e.2*v.2)) m).toList f =
        integral m.toList f+e.2*integral b (fun v => f (merge e.1 v)) := by
    rw [fold_add_integral b (fun v : S × Nat => (merge e.1 v.1,e.2*v.2)) m f]
    apply congrArg (integral m.toList f + ·)
    induction b with
    | nil => simp
    | cons v b ih =>
      simp only [List.map_cons,List.sum_cons,integral_cons,Nat.mul_add,Nat.mul_assoc] at ih ⊢
      rw [ih]
  have outer (m : Std.HashMap S Nat) :
      integral (a.foldl (fun m e => b.foldl (fun m v => add m (merge e.1 v.1) (e.2*v.2)) m) m).toList f =
        integral m.toList f+integral a (fun s => integral b (fun v => f (merge s v))) := by
    induction a generalizing m with
    | nil => simp
    | cons e a ih =>
      simp only [List.foldl_cons,ih,inner,integral_cons]
      omega
  rw [convolve,outer,WeightedDP.integral_convolve]
  simp [integral]

def dp (initial : S) (merge : S → S → S) (feature : A → S) : List (List A) → Table S
  | [] => [(initial,1)]
  | xs::files => convolve merge (dp initial merge feature files) (histogram xs feature)

/-- Every file, local configuration and convolution transition is included;
the refinement holds for all weights and all states, including absent ones. -/
theorem dp_integral (initial : S) (merge : S → S → S) (feature : A → S)
    (files : List (List A)) (f : S → Nat) : integral (dp initial merge feature files) f =
      integral (WeightedDP.dp initial merge feature files) f := by
  induction files generalizing f with
  | nil => rfl
  | cons xs files ih =>
    rw [dp,convolve_integral,WeightedDP.integral_convolve]
    simp_rw [histogram_integral]
    rw [ih]
    exact (WeightedDP.integral_convolve _ _ _ _).symm

end ChuShogi.HashAggregation
