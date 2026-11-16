import ChuShogi.WeightedBranches

/-! Linear scans of an explicit branch-weight list. Branch weights are computed
once, before scanning; no repeated prefix-sum evaluation is used by unranking.
-/
namespace ChuShogi.LinearWeightedBranches

abbrev Choice (weights : List Nat) := Σ i : Fin weights.length, Fin weights[i.val]

def total (weights : List Nat) : Nat := weights.foldl (· + ·) 0
theorem total_eq_sum (weights : List Nat) : total weights=weights.sum := List.sum_eq_foldl_nat.symm

@[noinline] def unrank : (weights : List Nat) → Fin weights.sum → Choice weights
  | [],i => Fin.elim0 i
  | w::ws,i =>
    if h : i.val<w then ⟨0,⟨i.val,h⟩⟩
    else
      let q := unrank ws ⟨i.val-w,by have hi := i.isLt; change i.val<w+ws.sum at hi; omega⟩
      ⟨q.1.succ,q.2⟩

@[noinline] def rank : (weights : List Nat) → Choice weights → Fin weights.sum
  | [],p => Fin.elim0 p.1
  | w::ws,⟨⟨0,_⟩,k⟩ => ⟨k.val,by have hk := k.isLt; change k.val<w at hk; change k.val<w+ws.sum; omega⟩
  | w::ws,⟨⟨j+1,hj⟩,k⟩ =>
    let q := rank ws ⟨⟨j,Nat.lt_of_succ_lt_succ hj⟩,k⟩
    ⟨w+q.val,by have hq := q.isLt; change w+q.val<w+ws.sum; omega⟩

theorem rank_unrank (weights : List Nat) (i : Fin weights.sum) : rank weights (unrank weights i)=i := by
  induction weights with
  | nil => exact Fin.elim0 i
  | cons w ws ih =>
    by_cases h : i.val<w
    · apply Fin.ext
      simp only [unrank,dite_eq_left h]
      rfl
    · have hi : i.val-w<ws.sum := by have hi := i.isLt; change i.val<w+ws.sum at hi; omega
      have hr := congrArg Fin.val (ih (⟨i.val-w,hi⟩ : Fin ws.sum))
      change (rank ws (unrank ws ⟨i.val-w,hi⟩)).val=i.val-w at hr
      apply Fin.ext
      simp only [unrank,dite_eq_right h]
      change w+(rank ws (unrank ws ⟨i.val-w,hi⟩)).val=i.val
      rw [hr]
      omega

theorem unrank_rank (weights : List Nat) (p : Choice weights) : unrank weights (rank weights p)=p := by
  induction weights with
  | nil => exact Fin.elim0 p.1
  | cons w ws ih =>
    rcases p with ⟨⟨j,hj⟩,k⟩
    cases j with
    | zero =>
      have hk : k.val<w := k.isLt
      change unrank (w::ws) ⟨k.val,_⟩=⟨⟨0,hj⟩,k⟩
      rw [unrank,dite_eq_left hk]
      rfl
    | succ j =>
      let tail : Choice ws := ⟨⟨j,Nat.lt_of_succ_lt_succ hj⟩,k⟩
      have hn : ¬w+(rank ws tail).val<w := by omega
      change unrank (w::ws) ⟨w+(rank ws tail).val,_⟩=⟨⟨j+1,hj⟩,k⟩
      rw [unrank,dite_eq_right hn]
      have he : (⟨w+(rank ws tail).val-w,by omega⟩ : Fin ws.sum)=rank ws tail := Fin.ext (by simp)
      rw [he,ih tail]
      rfl

def equivalence (weights : List Nat) : Fin weights.sum ≃ Choice weights where
  toFun := unrank weights
  invFun := rank weights
  left_inv := rank_unrank weights
  right_inv := unrank_rank weights

/-- Tail-recursive scanning retains a constant call stack even when the
summary list has over a million entries. -/
@[noinline] def locate : List Nat → Nat → Nat → Nat × Nat
  | [],i,offset => (offset,i)
  | w::ws,i,offset => if i<w then (offset,i) else locate ws (i-w) (offset+1)

def position (offset : Nat) {ws : List Nat} (p : Choice ws) : Nat × Nat := (offset+p.1.val,p.2.val)

theorem locate_correct (ws : List Nat) (i : Fin ws.sum) (offset : Nat) :
    locate ws i.val offset=position offset (unrank ws i) := by
  induction ws generalizing offset with
  | nil => exact Fin.elim0 i
  | cons w ws ih =>
    by_cases h : i.val<w
    · rw [locate,ite_eq_left h,unrank,dite_eq_left h]
      simp [position]
    · rw [locate,ite_eq_right h,unrank,dite_eq_right h]
      have hi : i.val-w<ws.sum := by have hi := i.isLt; change i.val<w+ws.sum at hi; omega
      have hh := ih (⟨i.val-w,hi⟩ : Fin ws.sum) (offset+1)
      exact hh.trans (by simp only [position,Fin.val_succ]; congr 1; omega)

@[noinline] def rankLoop : List Nat → Nat → Nat → Nat → Nat
  | [],_,value,acc => acc+value
  | _::_,0,value,acc => acc+value
  | w::ws,j+1,value,acc => rankLoop ws j value (acc+w)

theorem rankLoop_correct (ws : List Nat) (p : Choice ws) (acc : Nat) :
    rankLoop ws p.1.val p.2.val acc=acc+(rank ws p).val := by
  induction ws generalizing acc with
  | nil => exact Fin.elim0 p.1
  | cons w ws ih =>
    rcases p with ⟨⟨j,hj⟩,k⟩
    cases j with
    | zero => rfl
    | succ j =>
      change rankLoop ws j k.val (acc+w)=acc+(w+(rank ws ⟨⟨j,_⟩,k⟩).val)
      have hh := ih (⟨⟨j,Nat.lt_of_succ_lt_succ hj⟩,k⟩ : Choice ws) (acc+w)
      exact hh.trans (Nat.add_assoc _ _ _)

def fastUnrank (ws : List Nat) (i : Fin ws.sum) : Choice ws :=
  let q := locate ws i.val 0
  have he : q=((unrank ws i).1.val,(unrank ws i).2.val) := by simpa only [position,Nat.zero_add] using locate_correct ws i 0
  ⟨⟨q.1,by rw [he]; exact (unrank ws i).1.isLt⟩,
    ⟨q.2,by simpa only [congrArg Prod.fst he,congrArg Prod.snd he] using (unrank ws i).2.isLt⟩⟩

theorem fastUnrank_eq (ws : List Nat) (i : Fin ws.sum) : fastUnrank ws i=unrank ws i := by
  have he : locate ws i.val 0=((unrank ws i).1.val,(unrank ws i).2.val) := by
    simpa only [position,Nat.zero_add] using locate_correct ws i 0
  have hi : (fastUnrank ws i).1=(unrank ws i).1 := Fin.ext (congrArg Prod.fst he)
  apply Sigma.ext hi
  apply (Fin.heq_ext_iff (congrArg (fun j : Fin ws.length => ws[j.val]) hi)).mpr
  exact congrArg Prod.snd he

def fastRank (ws : List Nat) (p : Choice ws) : Fin ws.sum :=
  ⟨rankLoop ws p.1.val p.2.val 0,by rw [rankLoop_correct]; simp only [Nat.zero_add]; exact (rank ws p).isLt⟩

theorem fastRank_eq (ws : List Nat) (p : Choice ws) : fastRank ws p=rank ws p :=
  Fin.ext (by simp only [fastRank,rankLoop_correct,Nat.zero_add])

def fastEquivalence (weights : List Nat) : Fin weights.sum ≃ Choice weights where
  toFun := fastUnrank weights
  invFun := fastRank weights
  left_inv i := by rw [fastRank_eq,fastUnrank_eq,rank_unrank]
  right_inv p := by rw [fastUnrank_eq,fastRank_eq,unrank_rank]

/-- Map the original objects directly. Constructing weights by repeatedly
indexing a long linked list would make preparation quadratic. -/
def onList (xs : List A) (weight : A → Nat) :
    Fin (xs.map weight).sum ≃ Σ i : Fin xs.length, Fin (weight xs[i.val]) := by
  let ws := xs.map weight
  let convert : Choice ws ≃ Σ i : Fin xs.length, Fin (weight xs[i.val]) := {
    toFun p := ⟨⟨p.1.val,by simpa only [ws,List.length_map] using p.1.isLt⟩,
      ⟨p.2.val,by simpa only [ws,List.getElem_map] using p.2.isLt⟩⟩
    invFun p := ⟨⟨p.1.val,by simpa only [ws,List.length_map] using p.1.isLt⟩,
      ⟨p.2.val,by simpa only [ws,List.getElem_map] using p.2.isLt⟩⟩
    left_inv p := by apply Sigma.ext rfl; apply heq_of_eq; apply Fin.ext; rfl
    right_inv p := by apply Sigma.ext rfl; apply heq_of_eq; apply Fin.ext; rfl }
  exact (fastEquivalence ws).trans convert

def ofFunction {n : Nat} (weights : Fin n → Nat) : Fin (∑ i, weights i) ≃ Σ i : Fin n, Fin (weights i) := by
  let ws := List.ofFn weights
  let convert : Choice ws ≃ Σ i : Fin n, Fin (weights i) := {
    toFun p := ⟨Fin.cast (List.length_ofFn) p.1,
      Fin.cast (by simp [ws]; rfl) p.2⟩
    invFun p := ⟨Fin.cast (List.length_ofFn.symm) p.1,
      Fin.cast (by simp [ws]) p.2⟩
    left_inv p := by apply Sigma.ext (by apply Fin.ext; rfl); apply heq_of_eq; apply Fin.ext; simp
    right_inv p := by apply Sigma.ext (by apply Fin.ext; rfl); apply heq_of_eq; apply Fin.ext; simp }
  exact (finCongr List.sum_ofFn.symm).trans ((fastEquivalence ws).trans convert)

end ChuShogi.LinearWeightedBranches
