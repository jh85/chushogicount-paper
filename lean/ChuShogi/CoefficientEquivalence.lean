import ChuShogi.EGFConvolution

/-! Coefficient-table identities are extensional weighted-sum equalities;
insertion order of sparse keys has no mathematical significance. -/
namespace ChuShogi.CoefficientEquivalence
open EGFConvolution

def Equivalent (a b : Table) : Prop := ∀ f, integral a f = integral b f

theorem integral_unit (f : Degree → ℚ) : integral [(zero,1)] f = f zero := by simp [integral]

theorem degree_add_zero (s : Degree) : add s zero = s := by cases s; simp [add,zero]
theorem degree_zero_add (s : Degree) : add zero s = s := by cases s; simp [add,zero]
theorem degree_add_assoc (s t u : Degree) : add (add s t) u = add s (add t u) := by
  cases s; cases t; cases u; simp [add,Nat.add_assoc]

theorem degree_add_comm (s t : Degree) : add s t = add t s := by
  cases s; cases t; simp [add,Nat.add_comm]

theorem degree_add_swap (s t u : Degree) : add s (add t u) = add t (add s u) := by
  rw [← degree_add_assoc,degree_add_comm s t,degree_add_assoc]

theorem integral_cons (e : Term) (t : Table) (f : Degree → ℚ) :
    integral (e::t) f = e.2*f e.1+integral t f := rfl

theorem integral_zero (t : Table) : integral t (fun _ => 0) = 0 := by simp [integral]

theorem integral_add_test (t : Table) (f g : Degree → ℚ) :
    integral t (fun d => f d+g d) = integral t f+integral t g := by
  induction t with
  | nil => simp [integral]
  | cons e t ih => simp only [integral_cons,ih]; ring

theorem integral_mul_test (t : Table) (w : ℚ) (f : Degree → ℚ) :
    integral t (fun d => w*f d) = w*integral t f := by
  induction t with
  | nil => simp [integral]
  | cons e t ih => simp only [integral_cons,ih]; ring

theorem integral_exchange (a b : Table) (f : Degree → Degree → ℚ) :
    integral a (fun d => integral b (f d)) = integral b (fun e => integral a (fun d => f d e)) := by
  induction a with
  | nil => simp only [integral, List.map_nil,List.sum_nil]; simp
  | cons e a ih => simp only [integral_cons,integral_add_test,integral_mul_test,ih]

theorem convolve_congr (a a' b b' : Table) (ha : Equivalent a a') (hb : Equivalent b b') :
    Equivalent (convolve a b) (convolve a' b') := by
  intro f
  rw [integral_convolve,integral_convolve,ha]
  apply congrArg (integral a')
  funext s
  exact hb _

theorem unit_right (a : Table) : Equivalent (convolve a [(zero,1)]) a := by
  intro f
  rw [integral_convolve]
  apply congrArg (integral a)
  funext s
  simp [integral,degree_add_zero]

theorem unit_left (a : Table) : Equivalent (convolve [(zero,1)] a) a := by
  intro f
  rw [integral_convolve]
  simp [integral,degree_zero_add]

theorem convolve_assoc (a b c : Table) :
    Equivalent (convolve (convolve a b) c) (convolve a (convolve b c)) := by
  intro f
  simp_rw [integral_convolve,degree_add_assoc]

theorem convolve_comm (a b : Table) : Equivalent (convolve a b) (convolve b a) := by
  intro f
  rw [integral_convolve,integral_convolve,integral_exchange]
  apply congrArg (integral b)
  funext t
  apply congrArg (integral a)
  funext s
  rw [degree_add_comm]

theorem product_append (a b : List Table) :
    Equivalent (product (a++b)) (convolve (product a) (product b)) := by
  induction a with
  | nil => intro f; exact (unit_left (product b) f).symm
  | cons t ts ih =>
    intro f
    change integral (convolve t (product (ts++b))) f =
      integral (convolve (convolve t (product ts)) (product b)) f
    exact (convolve_congr t t _ _ (fun _ => rfl) ih f).trans
      (convolve_assoc t (product ts) (product b) f).symm

theorem product_permutation {ts us : List Table} (h : ts.Perm us) : Equivalent (product ts) (product us) := by
  induction h with
  | nil => intro _; rfl
  | cons t h ih => exact convolve_congr t t _ _ (fun _ => rfl) ih
  | swap t u ts =>
    intro f
    simp only [product,integral_convolve]
    rw [integral_exchange]
    apply congrArg (integral t)
    funext d
    apply congrArg (integral u)
    funext e
    apply congrArg (integral (product ts))
    funext g
    rw [degree_add_swap]
  | trans _ _ ih1 ih2 => intro f; exact (ih1 f).trans (ih2 f)

end ChuShogi.CoefficientEquivalence
