import ChuShogi.BoardDecomposition

/-! The concrete additive capacities are exactly the independent Board I4/I5
bounds, not merely a feature-vector convention in an isolated DP. -/
namespace ChuShogi.SummaryBridge
open Specification Promotion ConcreteDP BoardDecomposition

theorem labels_nodup (x : Fin 12) : (labels x).Nodup := by
  unfold labels
  split
  · decide
  · split <;> decide

theorem lookup_map {A : Type} [DecidableEq A] (ls : List A) (hn : ls.Nodup)
    (r : A → Nat) (a : A) :
    (((ls.zip (ls.map r)).filter fun (l,_) => decide (l = a)).map Prod.snd).sum =
      if a ∈ ls then r a else 0 := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    have ht := List.nodup_cons.mp hn
    simp only [List.map_cons,List.zip_cons_cons,List.filter_cons]
    by_cases he : l = a
    · subst a
      simp only [decide_true,ite_true,List.map_cons,List.sum_cons]
      rw [ih ht.2]
      simp [ht.1]
    · simp only [he,decide_false,Bool.false_eq_true,ite_false]
      rw [ih ht.2]
      simp [List.mem_cons,Ne.symm he]

/-- The concrete local lookup agrees with the independent Board projection. -/
theorem localU_boardLocal (b : Board) (hb : I1 b) (x : Fin 12) :
    localU (boardLocal b x) = unpromoted b x := by
  funext c k
  change ((((labels x).zip ((labels x).map fun l => unpromoted b x l.1 l.2)).filter
    fun (l,_) => decide (l = (c,k))).map Prod.snd).sum = _
  rw [lookup_map _ (labels_nodup x)]
  split
  · rfl
  · rename_i hn
    exact (absent_slot_zero b hb x c k (fun hs => hn ((labels_membership x c k).mpr hs))).symm

def cap (s : Summary) : Colour → Kind → Nat
  | .black,.pawn => s.cb | .white,.pawn => s.cw
  | .black,.lance => s.bL | .white,.lance => s.wL
  | .black,.chariot => s.bRC | .white,.chariot => s.wRC
  | .black,.goBetween => s.bGB | .white,.goBetween => s.wGB

theorem feature_cap (u : Local) (c : Colour) (k : Kind) : cap (feature u) c k = localCap u c k := by
  cases c <;> cases k <;> simp [cap,feature,localCap,HasSlot,pawn_eligibility]

theorem summary_cap (us : List Local) (c : Colour) (k : Kind) :
    cap (summary us) c k = (us.map fun u => localCap u c k).sum := by
  induction us with
  | nil => cases c <;> cases k <;> rfl
  | cons u us ih =>
    change cap (add (summary us) (feature u)) c k = _
    have ha (s t : Summary) : cap (add s t) c k = cap s c k + cap t c k := by
      cases c <;> cases k <;> rfl
    rw [ha,ih,feature_cap]
    simp [Nat.add_comm]

theorem sum_bits {A : Type} (xs : List A) (p : A → Prop) [DecidablePred p] :
    (xs.map fun x => bit (p x)).sum = (xs.filter fun x => decide (p x)).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.filter_cons]
    rw [ih]
    by_cases hp : p x <;> simp [bit,hp,Nat.add_comm]

def boardSummary (b : Board) : Summary := summary (boardTuple b)

theorem boardSummary_cap (b : Board) (hb : I1 b) (c : Colour) (k : Kind) :
    cap (boardSummary b) c k = (nonpawnFiles (unpromoted b) c k).length := by
  rw [boardSummary,summary_cap]
  simp only [boardTuple,List.map_map,Function.comp_def,localCap,localU_boardLocal b hb]
  change ((indices.map fun x => bit (HasSlot x c k ∧ Eligible (unpromoted b x) c k))).sum = _
  rw [sum_bits]
  simp [indices,nonpawnFiles,List.filter_reverse]

theorem summary_joint (us : List Local) :
    (summary us).joint = (us.map fun u =>
      bit (localU u .black .pawn = 0 ∧ localU u .white .pawn = 0)).sum := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    change (summary us).joint + (feature u).joint = _
    rw [ih]
    simp [feature,Nat.add_comm]

theorem boardSummary_joint (b : Board) (hb : I1 b) :
    (boardSummary b).joint = (pawnFiles (unpromoted b)).length := by
  rw [boardSummary,summary_joint]
  simp only [boardTuple,List.map_map,Function.comp_def,localU_boardLocal b hb]
  change ((indices.map fun x => bit (unpromoted b x .black .pawn = 0 ∧
    unpromoted b x .white .pawn = 0))).sum = _
  rw [sum_bits]
  simp [indices,pawnFiles,List.filter_reverse]

/-- I4/I5 are exactly bounds on the concrete summary's joint and type capacities. -/
theorem I4_I5_summary (b : Board) (hb : I1 b) : I4 b ∧ I5 b ↔
    (promotedNumber b .black .pawn + promotedNumber b .white .pawn ≤ (boardSummary b).joint) ∧
    (∀ c k, k ≠ .pawn → promotedNumber b c k ≤ cap (boardSummary b) c k) := by
  simp only [I4,I5,boardSummary_joint b hb,boardSummary_cap b hb]

end ChuShogi.SummaryBridge
