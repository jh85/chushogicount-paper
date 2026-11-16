import ChuShogi.ExecutableCounter

/-! Reordering complete file aggregations is sound for additive summaries.
This permits special files to be grouped before their capacity fields are
replaced by promoted-count polynomials. No supplied-table completeness premise.
-/
namespace ChuShogi.AggregationOrder
open WeightedDP

theorem integral_zero (t : Table S) : integral t (fun _ => 0) = 0 := by
  induction t with
  | nil => rfl
  | cons e t ih => simp [ih]

theorem integral_add (t : Table S) (f g : S → Nat) :
    integral t (fun s => f s+g s) = integral t f+integral t g := by
  induction t with
  | nil => rfl
  | cons e t ih => simp [ih,Nat.mul_add,Nat.add_assoc,Nat.add_left_comm]

theorem integral_mul (t : Table S) (w : Nat) (f : S → Nat) :
    integral t (fun s => w*f s) = w*integral t f := by
  induction t with
  | nil => simp
  | cons e t ih => simp [ih,Nat.mul_add,Nat.mul_left_comm]

theorem integral_exchange (a : Table S) (b : Table V) (f : S → V → Nat) :
    integral a (fun s => integral b (f s)) = integral b (fun v => integral a (fun s => f s v)) := by
  induction a with
  | nil => simp only [integral_nil,integral_zero]
  | cons e a ih =>
    simp only [integral_cons,integral_add,integral_mul,ih]

theorem dp_permutation [DecidableEq S] (initial : S) (merge : S → S → S) (feature : A → S)
    (assoc : ∀ x y z, merge (merge x y) z = merge x (merge y z))
    (comm : ∀ x y, merge x y = merge y x) {fs gs : List (List A)} (h : fs.Perm gs)
    (f : S → Nat) : integral (dp initial merge feature fs) f = integral (dp initial merge feature gs) f := by
  have swap (s x y : S) : merge (merge s x) y = merge (merge s y) x := by
    rw [assoc,assoc,comm x y]
  induction h generalizing f with
  | nil => rfl
  | cons xs h ih =>
    simp only [dp,integral_convolve]
    exact ih _
  | swap xs ys ts =>
    simp only [dp,integral_convolve]
    apply congrArg (integral (dp initial merge feature ts))
    funext s
    rw [integral_exchange]
    apply congrArg (integral (histogram ys feature))
    funext y
    apply congrArg (integral (histogram xs feature))
    funext x
    rw [swap]
  | trans h1 h2 ih1 ih2 => exact (ih1 f).trans (ih2 f)

theorem convolve_assoc [DecidableEq S] (merge : S → S → S)
    (assoc : ∀ x y z, merge (merge x y) z = merge x (merge y z))
    (a b c : Table S) (f : S → Nat) :
    integral (convolve merge (convolve merge a b) c) f =
      integral (convolve merge a (convolve merge b c)) f := by
  simp_rw [integral_convolve,assoc]

theorem dp_append [DecidableEq S] (initial : S) (merge : S → S → S) (feature : A → S)
    (assoc : ∀ x y z, merge (merge x y) z = merge x (merge y z))
    (unit : ∀ s, merge s initial = s) (fs gs : List (List A)) (f : S → Nat) :
    integral (dp initial merge feature (fs++gs)) f =
      integral (convolve merge (dp initial merge feature gs) (dp initial merge feature fs)) f := by
  induction fs generalizing f with
  | nil =>
    simp only [List.nil_append,dp,integral_convolve,integral_cons,integral_nil,Nat.one_mul,Nat.add_zero,unit]
  | cons xs fs ih =>
    simp only [List.cons_append,dp,integral_convolve]
    rw [ih]
    simp only [integral_convolve]
    simp_rw [assoc]

open ConcreteDP

theorem add_assoc (s t u : Summary) : add (add s t) u = add s (add t u) := by
  cases s; cases t; cases u; simp [add,Nat.add_assoc]

theorem add_comm (s t : Summary) : add s t = add t s := by
  cases s; cases t; simp [add,Nat.add_comm]

def plainIndices : List (Fin 12) := indices.filter fun x => decide (x.val ≠ 0 ∧ x.val ≠ 11 ∧ x.val ≠ 3 ∧ x.val ≠ 8)
def groupedIndices : List (Fin 12) := [11,0,8,3] ++ plainIndices

theorem indices_perm : groupedIndices.Perm indices := by decide

def reorderedTable : WeightedDP.Table Summary :=
  dp zero add CompactSummary.compactFeature (groupedIndices.map localConfigs)

/-- Grouping the two lance files and two go-between files first preserves every
completion-weighted total, before capacity-to-polynomial refinement. -/
theorem reordered_integral (f : Summary → Nat) :
    integral reorderedTable f = integral CompactSummary.compactTable f :=
  dp_permutation zero add CompactSummary.compactFeature add_assoc add_comm (indices_perm.map localConfigs) f

end ChuShogi.AggregationOrder
