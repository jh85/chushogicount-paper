import ChuShogi.EfficientCounter

/-! Cache binomial values as well as unrestricted placements. All caches are
constructed from their defining arithmetic; misses compute the same function.
The finite preload range is a performance choice, never a coverage assumption. -/
namespace ChuShogi.CachedArithmetic

def chooseReference (xs : List Nat) : Nat := (xs[0]?.getD 0).choose (xs[1]?.getD 0)
def chooseQueries : List (List Nat × Nat) :=
  (List.range 145).flatMap fun n => (List.range 145).map fun k => ([n,k],0)
def chooseCache : MemoizedSum.Cache := (MemoizedSum.run chooseReference chooseQueries ∅ 0).2

theorem chooseCache_sound : MemoizedSum.Sound chooseReference chooseCache := by
  apply (MemoizedSum.run_correct chooseReference chooseQueries ∅ 0 _).2
  intro k v h
  simp at h

def chooseWith (c : MemoizedSum.Cache) (n k : Nat) : Nat := (MemoizedSum.get chooseReference c [n,k]).1

theorem chooseWith_correct (n k : Nat) : chooseWith chooseCache n k = n.choose k :=
  (MemoizedSum.get_correct chooseReference chooseCache chooseCache_sound [n,k]).1

def term (c : MemoizedSum.Cache) (f0 f1 k : Nat) (d : EGFConvolution.Degree) (lab : Nat) : Nat :=
  lab*f0.descFactorial d.a0*f1.descFactorial d.a1*
    chooseWith c (k+d.m) d.m*chooseWith c (f0+f1-d.a0-d.a1) (k+d.m)

theorem term_correct (f0 f1 k : Nat) (d : EGFConvolution.Degree) (lab : Nat) :
    term chooseCache f0 f1 k d lab = UnrestrictedEvaluation.term f0 f1 k d lab := by
  simp only [term,chooseWith_correct,UnrestrictedEvaluation.term]

@[noinline] def fromCoefficients (cs : List (EGFConvolution.Degree × Nat)) (xs : List Nat) : Nat :=
  let c := chooseCache
  (cs.map fun e => term c (72-xs[0]?.getD 0) (72-xs[1]?.getD 0) (xs[2]?.getD 0) e.1 e.2).sum

def unrestricted (r : Bool) : List Nat → Nat := fromCoefficients (FreeEGF.labelledCoefficients r)

theorem unrestricted_correct (r : Bool) : unrestricted r = EfficientCounter.unrestricted r := by
  funext xs
  simp only [unrestricted,fromCoefficients,term_correct,EfficientCounter.unrestricted,UnrestrictedEvaluation.fromCoefficients]

def numerator (r : Bool) : Nat :=
  let cs := FreeEGF.labelledCoefficients r
  MemoizedSum.evaluate (fromCoefficients cs) (EfficientCounter.queries ReducedTables.table)
def count (r : Bool) : Nat := numerator r/64

theorem numerator_correct (r : Bool) : numerator r = EfficientCounter.numerator r := by
  change MemoizedSum.evaluate (unrestricted r) _ = _
  rw [unrestricted_correct]
  rfl

theorem count_correct (r : Bool) : count r = FiniteBoards.card (StructuralDecomposition.Stratum r) := by
  rw [count,numerator_correct]
  exact EfficientCounter.count_correct r

theorem count_C_r : count true = FiniteBoards.card Specification.C_r := count_correct true
theorem count_C_nr : count false = FiniteBoards.card Specification.C_nr := count_correct false

end ChuShogi.CachedArithmetic
