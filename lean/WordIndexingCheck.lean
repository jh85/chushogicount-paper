import ChuShogi.WordIndexing
open ChuShogi
def exampleCounts : Fin 2 → Nat := fun i => if i.val=0 then 2 else 1
theorem exampleWays : WordMultiplicity.ways 3 exampleCounts = 3 := by decide
#eval (List.finRange 3).map fun i =>
  let w := WordIndexing.unrank 3 exampleCounts (Fin.cast exampleWays.symm i)
  (List.finRange 3).map fun j => (w.val j).val
#eval WordMultiplicity.ways 3 (fun _ : Fin 2 => 0)
