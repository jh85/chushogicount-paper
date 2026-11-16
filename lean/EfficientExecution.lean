import ChuShogi.CachedArithmetic

/-! Compiled execution evidence; no literal integer theorem is asserted here. -/
def main : IO Unit := do
  let mut total : Nat := 0
  for r in [true,false] do
    let start ← IO.monoMsNow
    let n := ChuShogi.CachedArithmetic.numerator r
    IO.println s!"Royal stratum: {r}"
    IO.println s!"Scale remainder: {n % 64}"
    IO.println s!"Count: {n / 64}"
    IO.println s!"Elapsed milliseconds: {(← IO.monoMsNow) - start}"
    total := total + n / 64
  IO.println s!"Total candidates: {total}"
