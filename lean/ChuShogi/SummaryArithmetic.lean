import ChuShogi.FileBranchCoordinates

/-! Componentwise additive summary arithmetic for conditioned file selection. -/
namespace ChuShogi.SummaryArithmetic
open ConcreteDP

def LE (a b : Summary) : Prop :=
  a.uPB≤b.uPB ∧ a.uPW≤b.uPW ∧ a.cb≤b.cb ∧ a.cw≤b.cw ∧ a.joint≤b.joint ∧
  a.d0≤b.d0 ∧ a.d1≤b.d1 ∧ a.bL≤b.bL ∧ a.wL≤b.wL ∧ a.bRC≤b.bRC ∧ a.wRC≤b.wRC ∧ a.bGB≤b.bGB ∧ a.wGB≤b.wGB
instance (a b : Summary) : Decidable (LE a b) := inferInstanceAs (Decidable (_ ∧ _))
def sub (a b : Summary) : Summary :=
  ⟨a.uPB-b.uPB,a.uPW-b.uPW,a.cb-b.cb,a.cw-b.cw,a.joint-b.joint,a.d0-b.d0,a.d1-b.d1,
    a.bL-b.bL,a.wL-b.wL,a.bRC-b.bRC,a.wRC-b.wRC,a.bGB-b.bGB,a.wGB-b.wGB⟩

theorem add_eq_iff (a b t : Summary) : add a b=t ↔ LE a t ∧ b=sub t a := by
  cases a; cases b; cases t
  simp only [add,Summary.mk.injEq,LE,sub]
  omega

theorem sub_zero (s : Summary) : sub s zero=s := by cases s; simp [sub,zero]
theorem zero_le (s : Summary) : LE zero s := by simp [LE,zero]

end ChuShogi.SummaryArithmetic
