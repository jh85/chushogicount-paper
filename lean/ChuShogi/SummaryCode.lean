import ChuShogi.DPRenaming

/-! Lossless serialization of named fields, in the original source's sorted
eligibility-type order. The remaining Python provider correspondence is separate.
-/
namespace ChuShogi.SummaryCode
open Specification Promotion ConcreteDP SummaryBridge

def sourceTypes : List Label :=
  [(.black,.goBetween),(.black,.lance),(.black,.chariot),
   (.white,.goBetween),(.white,.lance),(.white,.chariot)]

def encode (s : Summary) : List Nat :=
  [s.uPB,s.uPW,s.cb,s.cw,s.joint,s.d0,s.d1,s.bGB,s.bL,s.bRC,s.wGB,s.wL,s.wRC]

def decode (xs : List Nat) : Summary :=
  ⟨xs[0]?.getD 0,xs[1]?.getD 0,xs[2]?.getD 0,xs[3]?.getD 0,xs[4]?.getD 0,
   xs[5]?.getD 0,xs[6]?.getD 0,xs[8]?.getD 0,xs[11]?.getD 0,xs[9]?.getD 0,
   xs[12]?.getD 0,xs[7]?.getD 0,xs[10]?.getD 0⟩

theorem decode_encode (s : Summary) : decode (encode s) = s := by cases s; rfl

theorem encode_injective : Function.Injective encode := by
  intro s t h
  have he := congrArg decode h
  simpa only [decode_encode] using he

theorem source_order (s : Summary) : encode s =
    [s.uPB,s.uPW,s.cb,s.cw,s.joint,s.d0,s.d1] ++ sourceTypes.map (fun (c,k) => cap s c k) := rfl

def merge (a b : List Nat) : List Nat := encode (add (decode a) (decode b))

theorem encode_add (s t : Summary) : encode (add s t) = merge (encode s) (encode t) := by
  simp only [merge,decode_encode]

/-- Hash-backed compact aggregation with the existing complete local lists. -/
def table : WeightedDP.Table (List Nat) := HashAggregation.dp (encode zero) merge
  (fun u => encode (CompactSummary.compactFeature u)) files

def groupTable (fs : List (List Local)) : WeightedDP.Table Summary :=
  (HashAggregation.dp (encode zero) merge (fun u => encode (CompactSummary.compactFeature u)) fs).map
    (fun e => (decode e.1,e.2))

theorem integral_decode (t : WeightedDP.Table (List Nat)) (f : Summary → Nat) :
    WeightedDP.integral (t.map fun e => (decode e.1,e.2)) f =
      WeightedDP.integral t (fun xs => f (decode xs)) := by
  unfold WeightedDP.integral
  rw [List.map_map]
  rfl

theorem group_integral (fs : List (List Local)) (f : Summary → Nat) :
    WeightedDP.integral (groupTable fs) f =
      WeightedDP.integral (WeightedDP.dp zero add CompactSummary.compactFeature fs) f := by
  rw [groupTable,integral_decode,HashAggregation.dp_integral]
  have he := DPRenaming.dp_integral_map zero add merge CompactSummary.compactFeature encode encode_add fs
    (fun xs => f (decode xs))
  simpa only [decode_encode] using he

theorem table_integral (f : Summary → Nat) :
    WeightedDP.integral table (fun xs => f (decode xs)) = WeightedDP.integral CompactSummary.compactTable f := by
  rw [table,HashAggregation.dp_integral]
  have he := DPRenaming.dp_integral_map zero add merge CompactSummary.compactFeature encode encode_add files
    (fun xs => f (decode xs))
  simpa only [decode_encode,CompactSummary.compactTable] using he

def count (r : Bool) : Nat :=
  let finish := ExecutableCounter.cachedEvaluator r
  WeightedDP.integral table (fun xs => finish (decode xs))

theorem count_reference (r : Bool) : count r = ExecutableCounter.countCompact r := table_integral _

theorem count_C_r : count true = FiniteBoards.card C_r := count_reference true |>.trans ExecutableCounter.count_C_r
theorem count_C_nr : count false = FiniteBoards.card C_nr := count_reference false |>.trans ExecutableCounter.count_C_nr

end ChuShogi.SummaryCode
