import ChuShogi.EGFArithmetic
import ChuShogi.GroupConfigurations

/-! Sparse, executable rational coefficient convolution. Keys store the number
of unrestricted pieces and the two numbers of forced pieces. Aggregating equal
keys adds coefficients; it does not discard distinct canonical role states. -/
namespace ChuShogi.EGFConvolution
open EGFArithmetic

structure Degree where
  m : Nat
  a0 : Nat
  a1 : Nat
  deriving DecidableEq, Repr

def zero : Degree := ⟨0,0,0⟩
def add (a b : Degree) : Degree := ⟨a.m+b.m,a.a0+b.a0,a.a1+b.a1⟩
abbrev Term := Degree × ℚ
abbrev Table := List Term

def integral (t : Table) (f : Degree → ℚ) : ℚ := (t.map fun e => e.2*f e.1).sum

def insert (s : Degree) (w : ℚ) : Table → Table
  | [] => [(s,w)]
  | (r,n)::t => if s=r then (r,w+n)::t else (r,n)::insert s w t

theorem integral_insert (s : Degree) (w : ℚ) (t : Table) (f : Degree → ℚ) :
    integral (insert s w t) f = w*f s + integral t f := by
  induction t with
  | nil => simp [insert,integral]
  | cons e t ih =>
    rcases e with ⟨r,n⟩
    simp only [insert]
    split
    · rename_i h; subst r; simp [integral,add_mul,add_assoc]
    · simp only [integral,List.map_cons,List.sum_cons] at ih ⊢
      rw [ih]
      ring

def convolve (a b : Table) : Table :=
  a.foldr (fun e out => b.foldr
    (fun v out => insert (add e.1 v.1) (e.2*v.2) out) out) []

theorem integral_convolve (a b : Table) (f : Degree → ℚ) :
    integral (convolve a b) f = integral a (fun s => integral b (fun v => f (add s v))) := by
  have inner (e : Term) (out : Table) :
      integral (b.foldr (fun v out => insert (add e.1 v.1) (e.2*v.2) out) out) f =
        e.2*integral b (fun v => f (add e.1 v)) + integral out f := by
    induction b with
    | nil => simp [integral]
    | cons v b ih =>
      simp only [List.foldr_cons]
      rw [integral_insert,ih]
      simp only [integral,List.map_cons,List.sum_cons]
      ring
  induction a with
  | nil => rfl
  | cons e a ih =>
    change integral (b.foldr _ (convolve a b)) f = _
    rw [inner,ih]
    rfl

def product : List Table → Table
  | [] => [(zero,1)]
  | t::ts => convolve t (product ts)

def tupleDegree : List Term → Degree
  | [] => zero
  | e::es => add e.1 (tupleDegree es)
def tupleWeight : List Term → ℚ
  | [] => 1
  | e::es => e.2*tupleWeight es

theorem sum_flatMap (xs : List α) (f : α → List ℚ) :
    (xs.flatMap f).sum = (xs.map fun x => (f x).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem mul_list_sum (w : ℚ) (xs : List α) (f : α → ℚ) :
    w*(xs.map f).sum = (xs.map fun x => w*f x).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [mul_add,ih]

/-- Every combination contributes exactly once before equal degrees are merged.
This is a complete product expansion, not consistency of a supplied table. -/
theorem product_expansion (ts : List Table) (f : Degree → ℚ) :
    integral (product ts) f =
      ((WeightedDP.tuples ts).map fun es => tupleWeight es*f (tupleDegree es)).sum := by
  induction ts generalizing f with
  | nil => simp [product,integral,WeightedDP.tuples,tupleWeight,tupleDegree]
  | cons t ts ih =>
    rw [product,integral_convolve]
    change (t.map fun e => e.2*integral (product ts) (fun v => f (add e.1 v))).sum = _
    simp_rw [ih]
    simp only [WeightedDP.tuples,List.map_flatMap,sum_flatMap,List.map_map,
      Function.comp_def,tupleWeight,tupleDegree,mul_list_sum,mul_assoc]

def Labelled (e : Term) : Prop := ∃ n : Nat, e.2*(e.1.m.factorial : ℚ) = n
def IntegralTable (t : Table) : Prop := ∀ e ∈ t, Labelled e

theorem labelled_add (s : Degree) (a b : ℚ) (ha : Labelled (s,a)) (hb : Labelled (s,b)) :
    Labelled (s,a+b) := by
  obtain ⟨n,hn⟩ := ha
  obtain ⟨m,hm⟩ := hb
  exact ⟨n+m,by simp only [Nat.cast_add,add_mul,← hn,← hm]⟩

theorem labelled_mul (a b : Term) (ha : Labelled a) (hb : Labelled b) :
    Labelled (add a.1 b.1,a.2*b.2) := by
  obtain ⟨n,hn⟩ := ha
  obtain ⟨m,hm⟩ := hb
  refine ⟨n*m*((a.1.m+b.1.m).choose a.1.m),?_⟩
  have hf : ((a.1.m+b.1.m).factorial : ℚ) =
      ((a.1.m+b.1.m).choose a.1.m : ℚ)*(a.1.m.factorial : ℚ)*(b.1.m.factorial : ℚ) := by
    have hh : (a.1.m+b.1.m).factorial =
        (a.1.m+b.1.m).choose a.1.m*a.1.m.factorial*b.1.m.factorial := by
      simpa only [Nat.add_sub_cancel_left] using (Nat.choose_mul_factorial_mul_factorial
        (n := a.1.m+b.1.m) (k := a.1.m) (by omega)).symm
    exact_mod_cast hh
  change a.2*b.2*((a.1.m+b.1.m).factorial : ℚ) = _
  rw [hf,Nat.cast_mul,Nat.cast_mul,← hn,← hm]
  ring

theorem integral_insert_closed (s : Degree) (w : ℚ) (t : Table)
    (hw : Labelled (s,w)) (ht : IntegralTable t) : IntegralTable (insert s w t) := by
  induction t with
  | nil =>
    intro e he
    simp only [insert,List.mem_singleton] at he
    subst e
    exact hw
  | cons v t ih =>
    have hv := ht v (by simp)
    have hh : IntegralTable t := fun e he => ht e (by simp [he])
    simp only [insert]
    split
    · rename_i h
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · subst s; exact labelled_add v.1 w v.2 hw hv
      · exact hh e he
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hv
      · exact ih hh e he

theorem convolve_integral (a b : Table) (ha : IntegralTable a) (hb : IntegralTable b) :
    IntegralTable (convolve a b) := by
  have inner (e : Term) (he : Labelled e) (out : Table) (ho : IntegralTable out) :
      IntegralTable (b.foldr (fun v out => insert (add e.1 v.1) (e.2*v.2) out) out) := by
    induction b with
    | nil => exact ho
    | cons v b ih =>
      apply integral_insert_closed
      · exact labelled_mul e v he (hb v (by simp))
      · exact ih (fun w hw => hb w (by simp [hw]))
  induction a with
  | nil => intro e he; cases he
  | cons e a ih =>
    apply inner e (ha e (by simp))
    exact ih (fun v hv => ha v (by simp [hv]))

theorem product_integral (ts : List Table) (h : ∀ t ∈ ts, IntegralTable t) :
    IntegralTable (product ts) := by
  induction ts with
  | nil => intro e he; simp only [product,List.mem_singleton] at he; subst e; exact ⟨1,by simp [zero]⟩
  | cons t ts ih =>
    exact convolve_integral t (product ts) (h t (by simp)) (ih (fun v hv => h v (by simp [hv])))

end ChuShogi.EGFConvolution
