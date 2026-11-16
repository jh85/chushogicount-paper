import ChuShogi.CompletionWordCodec
import ChuShogi.CompletionArithmetic
open ChuShogi ConcreteDP CompletionWordCodec

def emptySummary : Summary := ⟨0,0,12,12,12,0,0,2,2,2,2,2,2⟩
theorem sized : GroupCoverage.Sized emptySummary := by
  refine ⟨by decide,?_,rfl,rfl⟩
  intro c k hk
  cases c <;> cases k <;> simp_all [SummaryBridge.cap,emptySummary]

def main : IO Unit := do
  for r in [true,false] do
    let begin ← IO.monoMsNow
    let n := CompletionArithmetic.fromCoefficients (FreeEGF.labelledCoefficients r) emptySummary
    IO.println s!"royal={r} completion_interval={n}"
    (← IO.getStdout).flush
    if hn : 0<n then
      let e := evaluatorEquivalence r emptySummary sized
      for v in [0,n/2,n-1] do
        if hv : v<n then
          let i : Fin (EvaluatorRefinement.evaluateNat r emptySummary) := ⟨v,by
            rw [← CompletionArithmetic.fromCoefficients_correct r emptySummary]
            exact hv⟩
          let start ← IO.monoMsNow
          let w := e i
          let data := ((List.finRange 72).map w.val.1,(List.finRange 72).map w.val.2)
          let occupied := ((data.1++data.2).filter Option.isSome).length
          let back := e.symm w
          let stop ← IO.monoMsNow
          if back.val != v then throw (IO.userError "full completion inverse disagreed")
          IO.println s!"royal={r} pieces={occupied} inverse=true elapsed_ms={stop-start}"
          (← IO.getStdout).flush
    let finish ← IO.monoMsNow
    IO.println s!"royal={r} elapsed_ms={finish-begin}"
