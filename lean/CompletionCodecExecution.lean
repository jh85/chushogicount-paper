import ChuShogi.CompletionWordCodec
open ChuShogi ConcreteDP CompletionWordCodec

theorem zero_sized : GroupCoverage.Sized zero := by
  refine ⟨by decide,?_,rfl,rfl⟩
  intro c k _
  cases c <;> cases k <;> decide

def main : IO Unit := do
  for r in [true,false] do
    let start ← IO.monoMsNow
    let n := size r zero 2 2
    IO.println s!"royal={r} small-class interval={n}"
    if h : 0<n then
      let i : Fin n := ⟨0,h⟩
      let w := unrank r zero zero_sized 2 2 i
      let back := rank r zero zero_sized 2 2 w
      IO.println s!"first={repr ((List.finRange 2).map w.val.1,(List.finRange 2).map w.val.2)} inverse={back.val}"
    let stop ← IO.monoMsNow
    IO.println s!"elapsed_ms={stop-start}"
