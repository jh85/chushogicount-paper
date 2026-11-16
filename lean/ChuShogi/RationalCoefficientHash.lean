import Std.Data.HashMap.Lemmas
import ChuShogi.CoefficientEquivalence

/-! Hash-backed rational coefficient convolution. Complete weighted-sum
semantics is preserved for arbitrary tests; merging a key sums every canonical
contribution and does not assume integer intermediate coefficients. -/
namespace ChuShogi.RationalCoefficientHash
open EGFConvolution CoefficientEquivalence
instance : Hashable Degree := ⟨fun d => hash [d.m,d.a0,d.a1]⟩

def lookup (t : Table) (s : Degree) : ℚ := integral t (fun k => if k=s then 1 else 0)

theorem integral_perm (a b : Table) (h : a.Perm b) (f : Degree → ℚ) : integral a f=integral b f :=
  (h.map (fun e : Term => e.2*f e.1)).sum_eq

theorem lookup_cons (e : Term) (t : Table) (s : Degree) :
    lookup (e::t) s=e.2*(if e.1=s then 1 else 0)+lookup t s := rfl

theorem partition (t : Table) (s : Degree) (f : Degree → ℚ) : integral t f=
    lookup t s*f s+integral (t.filter fun e => !(s==e.1)) f := by
  induction t with
  | nil => simp [lookup,integral]
  | cons e t ih =>
    rcases e with ⟨k,v⟩
    by_cases h : k=s
    · subst k; simp [lookup_cons,integral_cons,ih,add_mul]; ring
    · have hn : s≠k := Ne.symm h
      simp [lookup_cons,h,hn,integral_cons,ih]; ring

theorem toList_nodup (m : Std.HashMap Degree ℚ) : m.toList.Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  apply m.distinct_keys_toList.imp
  intro a b h he
  cases he
  simp at h

theorem lookup_toList (m : Std.HashMap Degree ℚ) (s : Degree) : lookup m.toList s=m[s]?.getD 0 := by
  unfold lookup integral
  rw [← List.sum_toFinset _ (toList_nodup m)]
  cases hm : m[s]? with
  | none =>
    simp only [Option.getD_none]
    apply Finset.sum_eq_zero
    intro e he
    have hv := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp (List.mem_toFinset.mp he)
    by_cases hk : e.1=s
    · rw [hk,hm] at hv; cases hv
    · simp [hk]
  | some v =>
    simp only [Option.getD_some]
    have hs : (s,v)∈m.toList.toFinset := List.mem_toFinset.mpr (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hm)
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

def insert (m : Std.HashMap Degree ℚ) (s : Degree) (w : ℚ) : Std.HashMap Degree ℚ := m.insert s (w+m[s]?.getD 0)

theorem integral_insert (m : Std.HashMap Degree ℚ) (s : Degree) (w : ℚ) (f : Degree → ℚ) :
    integral (insert m s w).toList f=w*f s+integral m.toList f := by
  have hp := Std.HashMap.toList_insert_perm (m := m) (k := s) (v := w+m[s]?.getD 0)
  rw [insert,integral_perm _ _ hp,integral_cons,partition m.toList s f,lookup_toList,add_mul,add_assoc]
  simp
  apply congrArg (fun t => integral t f)
  apply List.filter_congr
  intro e _
  by_cases he : s=e.1
  · rw [he]; simp
  · have hb : (s==e.1)=false := by simp [he]
    simp [he,hb]

def convolve (a b : Table) : Table :=
  (a.foldl (fun m e => b.foldl (fun m v => insert m (EGFConvolution.add e.1 v.1) (e.2*v.2)) m) ∅).toList

theorem fold_insert (xs : List A) (make : A → Term) (m : Std.HashMap Degree ℚ) (f : Degree → ℚ) :
    integral (xs.foldl (fun m x => insert m (make x).1 (make x).2) m).toList f=
      integral m.toList f+(xs.map fun x => (make x).2*f (make x).1).sum := by
  induction xs generalizing m with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons,List.map_cons,List.sum_cons,ih,integral_insert]
    ring

theorem integral_convolve (a b : Table) (f : Degree → ℚ) : integral (convolve a b) f=
    integral a (fun s => integral b (fun t => f (EGFConvolution.add s t))) := by
  have inner (e : Term) (m : Std.HashMap Degree ℚ) :
      integral (b.foldl (fun m v => insert m (EGFConvolution.add e.1 v.1) (e.2*v.2)) m).toList f=
        integral m.toList f+e.2*integral b (fun v => f (EGFConvolution.add e.1 v)) := by
    rw [fold_insert b (fun v : Term => (EGFConvolution.add e.1 v.1,e.2*v.2)) m f]
    simp only [integral,mul_list_sum,mul_assoc]
  have outer (m : Std.HashMap Degree ℚ) :
      integral (a.foldl (fun m e => b.foldl (fun m v => insert m (EGFConvolution.add e.1 v.1) (e.2*v.2)) m) m).toList f=
        integral m.toList f+integral a (fun s => integral b (fun v => f (EGFConvolution.add s v))) := by
    induction a generalizing m with
    | nil => simp [integral]
    | cons e a ih =>
      simp only [List.foldl_cons,ih,inner,integral_cons]
      ring
  rw [convolve,outer]
  simp [integral]

theorem equivalent (a b : Table) : Equivalent (convolve a b) (EGFConvolution.convolve a b) := by
  intro f
  rw [integral_convolve,EGFConvolution.integral_convolve]

end ChuShogi.RationalCoefficientHash
