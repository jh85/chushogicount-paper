import ChuShogi.ValueCache
import ChuShogi.CompletionCoefficients

/-! Reuse exact placement factors across group-selection branches. The preload
is an optimization only: every miss computes the same proved placement formula.
-/
namespace ChuShogi.PlacementCache
open EGFConvolution

def encode (d : Degree) : List Nat := [d.m,d.a0,d.a1]
def decode (xs : List Nat) : Degree := ⟨xs[0]?.getD 0,xs[1]?.getD 0,xs[2]?.getD 0⟩
theorem decode_encode (d : Degree) : decode (encode d)=d := by cases d; rfl

def reference (n0 n1 : Nat) (xs : List Nat) : ℚ := CompletionCoefficients.placement n0 n1 (decode xs)
def queries : List (List Nat) := (List.range 145).flatMap fun m => (List.range 5).flatMap fun a0 =>
  (List.range 7).map fun a1 => [m,a0,a1]

structure Prepared (n0 n1 : Nat) where
  values : ValueCache.Cache ℚ
  sound : ValueCache.Sound (reference n0 n1) values

@[noinline] def prepare (n0 n1 : Nat) : Prepared n0 n1 :=
  ⟨ValueCache.prepare (reference n0 n1) queries,ValueCache.prepare_sound _ _⟩

@[noinline] def test (c : Prepared n0 n1) (d : Degree) : ℚ :=
  (ValueCache.get (reference n0 n1) c.values (encode d)).1

theorem test_correct (c : Prepared n0 n1) : test c=CompletionCoefficients.placement n0 n1 := by
  funext d
  rw [test,(ValueCache.get_correct _ _ c.sound _).1,reference,decode_encode]

end ChuShogi.PlacementCache
