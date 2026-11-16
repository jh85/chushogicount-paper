import ChuShogi.CachedArithmetic
import ChuShogi.CandidatePartition

/-! Primary manuscript integer certification with an explicitly expanded
computational trust boundary. These theorems use `native_decide` and therefore
trust Lean's compiler/runtime and native reduction mechanism, in addition to
the ordinary kernel/standard axioms. They are deliberately outside the main
ChuShogi import graph. `EfficientCounter.count_correct` itself uses only the
standard axioms. This is not a proof of every Python execution.

The native calculation constructs all local DP transitions, both complete
special polynomials, every reduced row and every admissible pawn query. It
starts with an empty cache and computes every miss. It does not check a supplied
partial state table or assume that supplied entries cover all states.
-/
namespace ChuShogi.NumericalCertification

set_option maxRecDepth 1000000

def reported_C_r : Nat :=
  191268797913333891330065995553675691619019251307357645954773256654516618748808675984141439531875112036039910149901581282707122183444296145463470850340851034075349792

def reported_C_nr : Nat :=
  1980652455929932338440020533783149804914160984693477930660462197612846617711822720340098312102549205699770822408956331542081038206237618818521412927374709499540192

theorem execution_C_r : CachedArithmetic.count true = reported_C_r := by native_decide
theorem execution_C_nr : CachedArithmetic.count false = reported_C_nr := by native_decide

theorem cardinality_C_r : FiniteBoards.card Specification.C_r = reported_C_r :=
  CachedArithmetic.count_C_r.symm.trans execution_C_r

theorem cardinality_C_nr : FiniteBoards.card Specification.C_nr = reported_C_nr :=
  CachedArithmetic.count_C_nr.symm.trans execution_C_nr

theorem combined_reported : reported_C_r+reported_C_nr =
  193249450369263823668506016087458841423933412292051123885433718852129465366520498704481537843977661241739680972310537614249203221650533764281992263268225743574889984 := by decide

theorem cardinality_candidates : FiniteBoards.card Specification.Candidate =
  193249450369263823668506016087458841423933412292051123885433718852129465366520498704481537843977661241739680972310537614249203221650533764281992263268225743574889984 := by
  rw [CandidatePartition.card_split,cardinality_C_r,cardinality_C_nr]
  exact combined_reported

#print axioms execution_C_r
#print axioms execution_C_nr
#print axioms cardinality_C_r
#print axioms cardinality_C_nr
#print axioms combined_reported
#print axioms cardinality_candidates
#print execution_C_r._native.native_decide.ax_1_1
#print execution_C_nr._native.native_decide.ax_1_1

end ChuShogi.NumericalCertification
