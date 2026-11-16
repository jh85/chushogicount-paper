import Std

/-!
A finite weighted file DP with no supplied-table completeness assumption.
`Valid` specifies tuples coordinatewise, independently of the recurrence.
Files are in reverse processing order: a new file is prepended to a tuple.
The summary extends the tail summary; no algebraic laws on `merge` are needed.
A table denotes a function on all states, including omitted states with zero weight.
-/
namespace ChuShogi.WeightedDP

variable {A S V : Type}

def Valid : List (A → Prop) → List A → Prop
  | [], xs => xs = []
  | p :: ps, xs => ∃ x tail, xs = x :: tail ∧ p x ∧ Valid ps tail

def tuples : List (List A) → List (List A)
  | [] => [[]]
  | xs :: files => xs.flatMap fun x => (tuples files).map (x :: ·)

def Enumerates : List (A → Prop) → List (List A) → Prop
  | [], [] => True
  | p :: ps, xs :: files => (∀ x, x ∈ xs ↔ p x) ∧ Enumerates ps files
  | _, _ => False

theorem tuples_iff (preds : List (A → Prop)) (files : List (List A))
    (h : Enumerates preds files) (u : List A) :
    u ∈ tuples files ↔ Valid preds u := by
  induction files generalizing preds u with
  | nil =>
    cases preds with
    | nil => simp [tuples, Valid]
    | cons p ps => exact False.elim h
  | cons xs files ih =>
    cases preds with
    | nil => exact False.elim h
    | cons p ps =>
      rcases h with ⟨hp, ht⟩
      simp only [tuples, List.mem_flatMap, List.mem_map, Valid]
      constructor
      · rintro ⟨x, hx, tail, hu, rfl⟩
        exact ⟨x, tail, rfl, (hp x).mp hx, (ih ps ht tail).mp hu⟩
      · rintro ⟨x, tail, rfl, hx, hu⟩
        exact ⟨x, (hp x).mpr hx, tail, (ih ps ht tail).mpr hu, rfl⟩

/-- Every tuple occurs once when every local configuration occurs once. -/
theorem tuples_nodup (files : List (List A))
    (h : ∀ xs ∈ files, xs.Nodup) : (tuples files).Nodup := by
  induction files with
  | nil => simp [tuples]
  | cons xs files ih =>
    have hx := h xs (by simp)
    have ht := ih (fun ys hy => h ys (by simp [hy]))
    simp only [tuples, List.nodup_iff_pairwise_ne, List.pairwise_flatMap,
      List.pairwise_map]
    constructor
    · intro x _
      apply List.Pairwise.imp _ ht
      intro a b hab heq
      exact hab (List.cons.inj heq).2
    · apply List.Pairwise.imp _ hx
      intro x y hxy u hu v hv heq
      rcases List.mem_map.mp hu with ⟨us, _, rfl⟩
      rcases List.mem_map.mp hv with ⟨vs, _, rfl⟩
      exact hxy (List.cons.inj heq).1

abbrev Table (S : Type) := List (S × Nat)

def integral (t : Table S) (f : S → Nat) : Nat :=
  (t.map fun e => e.2 * f e.1).sum

@[simp] theorem integral_nil (f : S → Nat) : integral [] f = 0 := rfl
@[simp] theorem integral_cons (e : S × Nat) (t : Table S) (f : S → Nat) :
    integral (e :: t) f = e.2 * f e.1 + integral t f := rfl

/-- Add weights by key, without preserving alternative origin assignments. -/
def insert [DecidableEq S] (s : S) (w : Nat) : Table S → Table S
  | [] => [(s, w)]
  | (r, n) :: t => if s = r then (r, w + n) :: t else (r, n) :: insert s w t

theorem integral_insert [DecidableEq S] (s : S) (w : Nat) (t : Table S) (f : S → Nat) :
    integral (insert s w t) f = w * f s + integral t f := by
  induction t with
  | nil => simp [insert]
  | cons e t ih =>
    rcases e with ⟨r, n⟩
    simp only [insert]
    split
    · rename_i h; subst r; simp [Nat.add_mul, Nat.add_assoc]
    · simp only [integral_cons, ih]; omega

/-- Construct a complete local histogram from actual local objects. -/
def histogram [DecidableEq S] (xs : List A) (feature : A → S) : Table S :=
  xs.foldr (fun x t => insert (feature x) 1 t) []

theorem integral_histogram [DecidableEq S] (xs : List A) (feature : A → S) (f : S → Nat) :
    integral (histogram xs feature) f = (xs.map fun x => f (feature x)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change integral (insert (feature x) 1 (histogram xs feature)) f = _
    rw [integral_insert, ih]
    simp

/-- Weighted convolution with duplicate keys merged. -/
def convolve [DecidableEq S] (merge : S → V → S) (t : Table S) (a : Table V) : Table S :=
  t.foldr (fun e out => a.foldr
    (fun v out => insert (merge e.1 v.1) (e.2 * v.2) out) out) []

theorem integral_convolve [DecidableEq S] (merge : S → V → S) (t : Table S) (a : Table V)
    (f : S → Nat) :
    integral (convolve merge t a) f =
      integral t (fun s => integral a (fun v => f (merge s v))) := by
  have inner (e : S × Nat) (out : Table S) :
      integral (a.foldr (fun v out => insert (merge e.1 v.1) (e.2 * v.2) out) out) f =
        e.2 * integral a (fun v => f (merge e.1 v)) + integral out f := by
    induction a with
    | nil => simp
    | cons v a ih =>
      simp only [List.foldr_cons, integral_insert, integral_cons, ih]
      simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
  induction t with
  | nil => rfl
  | cons e t ih =>
    change integral (a.foldr _ (convolve merge t a)) f = _
    rw [inner, ih, integral_cons]

def summary (initial : S) (merge : S → V → S) (feature : A → V) : List A → S
  | [] => initial
  | x :: xs => merge (summary initial merge feature xs) (feature x)

def dp [DecidableEq S] [DecidableEq V] (initial : S) (merge : S → V → S) (feature : A → V) :
    List (List A) → Table S
  | [] => [(initial, 1)]
  | xs :: files => convolve merge (dp initial merge feature files) (histogram xs feature)

theorem sum_add (ys : List V) (g h : V → Nat) :
    (ys.map fun y => g y + h y).sum = (ys.map g).sum + (ys.map h).sum := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_exchange (xs : List A) (ys : List V) (f : A → V → Nat) :
    (xs.map fun x => (ys.map fun y => f x y).sum).sum =
      (ys.map fun y => (xs.map fun x => f x y).sum).sum := by
  induction xs with
  | nil =>
    induction ys with
    | nil => rfl
    | cons y ys ih => simpa using ih
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    exact (sum_add _ _ _).symm

theorem sum_flatMap (xs : List A) (f : A → List Nat) :
    (xs.flatMap f).sum = (xs.map fun x => (f x).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- The invariant for arbitrary test weights, hence for every summary state. -/
theorem dp_integral [DecidableEq S] [DecidableEq V] (initial : S) (merge : S → V → S)
    (feature : A → V) (files : List (List A)) (f : S → Nat) :
    integral (dp initial merge feature files) f =
      ((tuples files).map fun u => f (summary initial merge feature u)).sum := by
  induction files generalizing f with
  | nil => simp [dp, tuples, summary]
  | cons xs files ih =>
    rw [dp, integral_convolve]
    simp only [integral_histogram]
    rw [ih]
    rw [sum_exchange]
    simp only [tuples, List.map_flatMap, sum_flatMap, List.map_map]
    rfl

def lookup [DecidableEq S] (t : Table S) (s : S) : Nat := integral t (fun r => if r = s then 1 else 0)

theorem dp_initial [DecidableEq S] [DecidableEq V] (initial : S) (merge : S → V → S)
    (feature : A → V) (s : S) :
    lookup (dp initial merge feature []) s = if initial = s then 1 else 0 := by
  simp [lookup, dp]

/-- Sum over every old-state/local-feature pair whose merged state is s. -/
theorem dp_update [DecidableEq S] [DecidableEq V] (initial : S) (merge : S → V → S)
    (feature : A → V) (files : List (List A)) (xs : List A) (s : S) :
    lookup (dp initial merge feature (xs :: files)) s =
      integral (dp initial merge feature files) (fun r =>
        integral (histogram xs feature) (fun v => if merge r v = s then 1 else 0)) :=
  integral_convolve _ _ _ _

/-- Counts tuples of each summary, also when the state is absent from the table. -/
theorem dp_counts [DecidableEq S] [DecidableEq V] (initial : S) (merge : S → V → S)
    (feature : A → V) (files : List (List A)) (s : S) :
    lookup (dp initial merge feature files) s =
      ((tuples files).filter (fun u => decide (summary initial merge feature u = s))).length := by
  rw [lookup, dp_integral]
  induction tuples files with
  | nil => rfl
  | cons u us ih =>
    simp only [List.map_cons, List.sum_cons]
    split <;> simp_all [Nat.add_comm]

/-- A duplicate-free enumeration of the independently specified summary fibre. -/
theorem dp_fibre [DecidableEq S] [DecidableEq V]
    (initial : S) (merge : S → V → S) (feature : A → V)
    (preds : List (A → Prop)) (files : List (List A))
    (hc : Enumerates preds files) (hn : ∀ xs ∈ files, xs.Nodup) (s : S) :
    let fibre := (tuples files).filter (fun u => decide (summary initial merge feature u = s))
    fibre.Nodup ∧
    (∀ u, u ∈ fibre ↔ Valid preds u ∧ summary initial merge feature u = s) ∧
    lookup (dp initial merge feature files) s = fibre.length := by
  dsimp only
  refine ⟨(tuples_nodup files hn).filter _, ?_, dp_counts _ _ _ _ _⟩
  intro u
  simp [tuples_iff preds files hc u]

end ChuShogi.WeightedDP
