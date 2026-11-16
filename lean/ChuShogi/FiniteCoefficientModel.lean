import ChuShogi.FreeEGF

/-! Compositional coefficient refinement for independently specified finite
canonical choices. Constructors below prove complete sums, rather than checking
only entries of an externally supplied coefficient table. -/
namespace ChuShogi.FiniteCoefficientModel
open EGFConvolution
open scoped Classical

structure Model (A : Type) [Fintype A] where
  key : A → Degree
  weight : A → ℚ
  table : Table
  correct : ∀ f : Degree → ℚ, integral table f = ∑ a, weight a*f (key a)

def fromList {A : Type} [Fintype A] [DecidableEq A] (xs : List A) (hn : xs.Nodup)
    (hc : ∀ a, a ∈ xs) (key : A → Degree) (weight : A → ℚ) : Model A where
  key := key
  weight := weight
  table := xs.map fun a => (key a,weight a)
  correct f := by
    have he : xs.toFinset = Finset.univ := Finset.ext (fun a => by simp [hc a])
    simp only [integral,List.map_map,Function.comp_def]
    rw [← List.sum_toFinset _ hn,he]

def product {A B : Type} [Fintype A] [Fintype B] (a : Model A) (b : Model B) : Model (A × B) where
  key p := add (a.key p.1) (b.key p.2)
  weight p := a.weight p.1*b.weight p.2
  table := convolve a.table b.table
  correct f := by
    rw [integral_convolve,a.correct]
    simp_rw [b.correct]
    rw [Fintype.sum_prod_type]
    simp only [Finset.mul_sum,mul_assoc]

def relabel {A B : Type} [Fintype A] [Fintype B] (a : Model A) (e : A ≃ B) : Model B where
  key b := a.key (e.symm b)
  weight b := a.weight (e.symm b)
  table := a.table
  correct f := by
    rw [a.correct]
    exact Fintype.sum_equiv e _ _ (fun _ => by simp)

def unit : Model Unit where
  key _ := zero
  weight _ := 1
  table := [(zero,1)]
  correct f := by simp [integral]

noncomputable instance memberFintype {A : Type} [DecidableEq A] (xs : List A) :
    Fintype {a : A // a ∈ xs} := Fintype.ofList xs.attach (by intro a; simp)

noncomputable def members {A : Type} [DecidableEq A] (xs : List A) (hn : xs.Nodup)
    (key : A → Degree) (weight : A → ℚ) : Model {a : A // a ∈ xs} :=
  fromList xs.attach hn.attach (fun a => by simp) (fun a => key a.val) (fun a => weight a.val)

theorem members_table {A : Type} [DecidableEq A] (xs : List A) (hn : xs.Nodup)
    (key : A → Degree) (weight : A → ℚ) :
    (members xs hn key weight).table = xs.map fun a => (key a,weight a) := by
  simp [members,fromList]

def functionSplit (A : Type) (n : Nat) : (Fin (n+1) → A) ≃ A × (Fin n → A) where
  toFun f := (f 0,fun i => f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv _ := rfl

def emptyFunction (A : Type) : Unit ≃ (Fin 0 → A) where
  toFun _ i := Fin.elim0 i
  invFun _ := ()
  left_inv _ := rfl
  right_inv _ := by funext i; exact Fin.elim0 i

/-- Repeated independent group choices, constructed by proved product/relabel
operations, with no finite-product enumeration oracle. -/
def power {A : Type} [Fintype A] (a : Model A) : (n : Nat) → Model (Fin n → A)
  | 0 => relabel unit (emptyFunction A)
  | n+1 => relabel (product a (power a n)) (functionSplit A n).symm

theorem power_table {A : Type} [Fintype A] (a : Model A) (n : Nat) :
    (power a n).table = EGFConvolution.product (List.replicate n a.table) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change convolve a.table (power a n).table = _
    rw [ih]
    rfl

theorem power_key {A : Type} [Fintype A] (a : Model A) (n : Nat) (f : Fin n → A) :
    (power a n).key f = (List.ofFn fun i => a.key (f i)).foldr add zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change add (a.key (f 0)) ((power a n).key (fun i => f i.succ)) = _
    rw [List.ofFn_succ]
    exact congrArg (add (a.key (f 0))) (ih (fun i => f i.succ))

theorem power_weight {A : Type} [Fintype A] (a : Model A) (n : Nat) (f : Fin n → A) :
    (power a n).weight f = (List.ofFn fun i => a.weight (f i)).prod := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change a.weight (f 0)*(power a n).weight (fun i => f i.succ) = _
    rw [List.ofFn_succ,List.prod_cons,ih]

end ChuShogi.FiniteCoefficientModel
