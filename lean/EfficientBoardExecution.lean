import ChuShogi.EfficientBoardCodec
open ChuShogi ConcreteDP Specification EfficientBoardCodec

private def progress (message : String) : IO Unit := do
  IO.println message
  (← IO.getStdout).flush

def main : IO Unit := do
  let start ← IO.monoMsNow
  let plan := FileSuffixPlan.prepare files
  let nrows := (FileSuffixPlan.rows plan).length
  let nindex := (FileSuffixPlan.index plan).size
  let built ← IO.monoMsNow
  progress s!"suffix_rows={nrows} indexed={nindex} preparation_ms={built-start}"
  for r in [true,false] do
    let begun ← IO.monoMsNow
    let completion := CompletionCache.prepare r (FileSuffixPlan.rows plan)
    let uc := completion.uu.size
    let pc := completion.polynomials.size
    let fc := completion.completions.size
    let cached ← IO.monoMsNow
    progress s!"royal={r} uu_cache={uc} polynomial_cache={pc} completion_cache={fc} cache_ms={cached-begun}"
    let prepared : Prepared r := ⟨plan,completion⟩
    let n := size prepared
    let rt := runtime prepared
    progress s!"royal={r} interval={n}"
    if hn : 0<n then
      for v in [0,n/2,n-1] do
        if hv : v<n then
          let i : Fin (CachedArithmetic.count r) := ⟨v,by rw [← size_counter prepared]; exact hv⟩
          let t0 ← IO.monoMsNow
          let b := unrank rt i
          let placements := squares.map b.val
          let occupied := (placements.filter Option.isSome).length
          let back := rank rt b
          let t1 ← IO.monoMsNow
          if back.val != v then throw (IO.userError "whole-Board inverse execution disagreed")
          progress s!"royal={r} index={v} pieces={occupied} roundtrip=true elapsed_ms={t1-t0}"
    let endStratum ← IO.monoMsNow
    progress s!"royal={r} stratum_elapsed_ms={endStratum-begun}"
