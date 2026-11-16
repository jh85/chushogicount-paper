import ChuShogi.GroupedFiles

/-! Key invariants of the constructed DP, independent of a supplied table.
They justify dropping capacity fields that are zero throughout a file group. -/
namespace ChuShogi.TableInvariant
open WeightedDP

def Keys (P : S → Prop) (t : Table S) : Prop := ∀ e ∈ t, P e.1

theorem insert_keys [DecidableEq S] (P : S → Prop) (s : S) (w : Nat) (t : Table S)
    (hs : P s) (ht : Keys P t) : Keys P (WeightedDP.insert s w t) := by
  induction t with
  | nil => intro e he; simp only [WeightedDP.insert,List.mem_singleton] at he; subst e; exact hs
  | cons e t ih =>
    have he := ht e (by simp)
    have hh : Keys P t := fun v hv => ht v (by simp [hv])
    simp only [WeightedDP.insert]
    split
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact he
      · exact hh v hv
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact he
      · exact ih hh v hv

theorem histogram_keys [DecidableEq S] (P : S → Prop) (xs : List A) (feature : A → S)
    (h : ∀ x ∈ xs, P (feature x)) : Keys P (histogram xs feature) := by
  induction xs with
  | nil => intro e he; cases he
  | cons x xs ih =>
    apply insert_keys P _ _ _ (h x (by simp))
    exact ih (fun y hy => h y (by simp [hy]))

theorem convolve_keys_rel [DecidableEq S] (P Q R : S → Prop) (merge : S → S → S)
    (a b : Table S) (ha : Keys P a) (hb : Keys Q b)
    (hm : ∀ s t, P s → Q t → R (merge s t)) : Keys R (convolve merge a b) := by
  have inner (e : S × Nat) (he : P e.1) (out : Table S) (ho : Keys R out) :
      Keys R (b.foldr (fun v out => WeightedDP.insert (merge e.1 v.1) (e.2*v.2) out) out) := by
    induction b with
    | nil => exact ho
    | cons v b ih =>
      apply insert_keys R _ _ _ (hm _ _ he (hb v (by simp)))
      exact ih (fun w hw => hb w (by simp [hw]))
  induction a with
  | nil => intro e he; cases he
  | cons e a ih =>
    apply inner e (ha e (by simp))
    exact ih (fun v hv => ha v (by simp [hv]))

theorem convolve_keys [DecidableEq S] (P : S → Prop) (merge : S → S → S)
    (a b : Table S) (ha : Keys P a) (hb : Keys P b)
    (hm : ∀ s t, P s → P t → P (merge s t)) : Keys P (convolve merge a b) :=
  convolve_keys_rel P P P merge a b ha hb hm

theorem dp_keys [DecidableEq S] (P : S → Prop) (initial : S) (merge : S → S → S)
    (feature : A → S) (files : List (List A)) (h0 : P initial)
    (hm : ∀ s t, P s → P t → P (merge s t))
    (hf : ∀ xs ∈ files, ∀ x ∈ xs, P (feature x)) : Keys P (dp initial merge feature files) := by
  induction files with
  | nil => intro e he; simp only [dp,List.mem_singleton] at he; subst e; exact h0
  | cons xs files ih =>
    apply convolve_keys P merge _ _ (ih (fun ys hy => hf ys (by simp [hy])))
      (histogram_keys P xs feature (hf xs (by simp))) hm

theorem dp_bound [DecidableEq S] (measure : S → Nat) (initial : S) (merge : S → S → S)
    (feature : A → S) (files : List (List A)) (h0 : measure initial = 0)
    (hm : ∀ s t, measure (merge s t) = measure s+measure t)
    (hf : ∀ xs ∈ files, ∀ x ∈ xs, measure (feature x) ≤ 1) :
    Keys (fun s => measure s ≤ files.length) (dp initial merge feature files) := by
  induction files with
  | nil =>
    intro e he
    simp only [dp,List.mem_singleton] at he
    subst e
    exact Nat.le_of_eq h0
  | cons xs files ih =>
    apply convolve_keys_rel (fun s => measure s ≤ files.length) (fun s => measure s ≤ 1)
      (fun s => measure s ≤ (xs::files).length) merge _ _
      (ih (fun ys hy => hf ys (by simp [hy]))) (histogram_keys _ xs feature (hf xs (by simp)))
    intro s t hs ht
    rw [hm]
    simp only [List.length_cons]
    omega

end ChuShogi.TableInvariant
