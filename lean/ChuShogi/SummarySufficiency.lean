import ChuShogi.Completion

/-! Concrete summary sufficiency for actual Candidate Boards. The geometry,
material invariance and promotion bounds are all discharged by proved lemmas. -/
namespace ChuShogi.SummarySufficiency
open Specification Promotion ConcreteDP BoardDecomposition SummaryBridge
open ResidualSquares OccupancyBridge Placement Completion

 theorem classCount_eq (b : Board) (c : Colour) (r : Role) (a : Nat) :
    countWhere b c r (fun s => decide (squareClass s = a)) =
      classMultiplicity squares squareClass b a (c,r) := by
  unfold countWhere classMultiplicity
  congr 1
  apply List.filter_congr
  intro s _
  by_cases hp : b s = some (c,r) <;> by_cases ha : squareClass s = a <;> simp [hp,ha]

theorem transport_classCount (u v f : Board) (e : ResidualSquares.Relabelling u v)
    (c : Colour) (r : Role) (a : Nat) :
    countWhere (transport e.toRelabelling f) c r (fun s => decide (squareClass s = a)) =
      countWhere f c r (fun s => decide (squareClass s = a)) := by
  rw [classCount_eq,classCount_eq]
  have hp := FiniteRelabelling.forward_perm squares Rendering.squares_nodup mem_squares e.toRelabelling
  have hm := classMultiplicity_transport e.toRelabelling squares f a (c,r)
  have he : classMultiplicity (squares.map e.forward) squareClass (transport e.toRelabelling f) a (c,r) =
      classMultiplicity squares squareClass (transport e.toRelabelling f) a (c,r) :=
    (hp.filter _).length_eq
  rwa [he] at hm

theorem transport_I6 (u v f : Board) (e : ResidualSquares.Relabelling u v) :
    I6 (transport e.toRelabelling f) ↔ I6 f := by
  simp only [I6,transport_classCount]

theorem transport_I7 (u v f : Board) (e : ResidualSquares.Relabelling u v) :
    I7 (transport e.toRelabelling f) ↔ I7 f := by
  constructor
  · intro h s c hs
    have he : transport e.toRelabelling f (e.forward s) = some (c,.native .kirin) := by
      simpa only [transport,e.left_inverse] using hs
    have ha := h (e.forward s) c he
    rwa [e.preserves_class] at ha
  · intro h s c hs
    have ha := h (e.backward s) c hs
    have he := e.preserves_class (e.backward s)
    rw [e.right_inverse] at he
    exact he.trans ha

theorem transport_conditions (u v f : Board) (e : ResidualSquares.Relabelling u v) (s : Summary) :
    FreeConditions s (transport e.toRelabelling f) ↔ FreeConditions s f := by
  simp only [FreeConditions,Bounds,promotedNumber,transport_number,transport_I6,transport_I7,
    I8,hasRoyal,I9]

def inverse (u v : Board) (e : ResidualSquares.Relabelling u v) : ResidualSquares.Relabelling v u where
  forward := e.backward
  backward := e.forward
  left_inverse := e.right_inverse
  right_inverse := e.left_inverse
  preserves_class s := by
    have h := e.preserves_class (e.backward s)
    rw [e.right_inverse] at h
    exact h.symm
  preserves_available := backward_available u v e

theorem transport_completion (u v f : Board)
    (hu : OnlyConfined u) (hv : OnlyConfined v)
    (hu1 : I1 u) (hu2 : I2 u) (hu3 : I3 u) (hv1 : I1 v) (hv2 : I2 v) (hv3 : I3 v)
    (he : boardSummary u = boardSummary v) (e : ResidualSquares.Relabelling u v)
    (hc : Completes u f) : Completes v (transport e.toRelabelling f) := by
  obtain ⟨hf,hd,hfcond⟩ := (completes_iff u f hu hu1 hu2 hu3).mp hc
  apply (completes_iff v _ hv hv1 hv2 hv3).mpr
  refine ⟨transport_onlyFree u v f e hf,transport_disjoint u v f e hd,?_⟩
  rw [transport_conditions,← he]
  exact hfcond

/-- A concrete bijection between all candidate completions of equal-summary
valid confined Boards. No residual-square or material-invariance premise remains. -/
def completionIso (u v : Board)
    (hu : OnlyConfined u) (hv : OnlyConfined v)
    (hu1 : I1 u) (hu2 : I2 u) (hu3 : I3 u) (hv1 : I1 v) (hv2 : I2 v) (hv3 : I3 v)
    (he : boardSummary u = boardSummary v) :
    FiniteRelabelling.Iso {f : Board // Completes u f} {f : Board // Completes v f} := by
  let e := of_summary u v hu1 hv1 hu hv he
  refine ⟨(fun f => ⟨transport e.toRelabelling f.val,
    transport_completion u v f.val hu hv hu1 hu2 hu3 hv1 hv2 hv3 he e f.property⟩),
    (fun f => ⟨transport (inverse u v e).toRelabelling f.val,
    transport_completion v u f.val hv hu hv1 hv2 hv3 hu1 hu2 hu3 he.symm (inverse u v e) f.property⟩),?_,?_⟩
  · intro f
    apply Subtype.ext
    exact Placement.transport_inverse e.toRelabelling f.val
  · intro f
    apply Subtype.ext
    exact Placement.inverse_transport e.toRelabelling f.val

/-- The two royal strata are distinguished by present kings, not origins. -/
def RoyalMode (r : Bool) (f : Board) : Prop := if r then hasRoyal f .black else ¬ hasRoyal f .black

def StratumCompletes (r : Bool) (u f : Board) : Prop :=
  OnlyFree f ∧ Disjoint u f ∧ (if r then C_r (merge u f) else C_nr (merge u f))

theorem stratum_iff (r : Bool) (u f : Board) (hu : OnlyConfined u) :
    StratumCompletes r u f ↔ Completes u f ∧ RoyalMode r f := by
  cases r <;> unfold StratumCompletes Completes RoyalMode C_r C_nr
  all_goals
    simp only [Bool.false_eq_true,ite_false,ite_true]
    constructor
    · rintro ⟨hf,hd,hc,hr⟩
      exact ⟨⟨hf,hd,hc⟩,by simpa only [merge_royal u f hu hf hd .black] using hr⟩
    · rintro ⟨⟨hf,hd,hc⟩,hr⟩
      exact ⟨hf,hd,hc,by simpa only [merge_royal u f hu hf hd .black] using hr⟩

theorem transport_royalMode (r : Bool) (u v f : Board) (e : ResidualSquares.Relabelling u v) :
    RoyalMode r (transport e.toRelabelling f) ↔ RoyalMode r f := by
  cases r <;> simp only [RoyalMode,Bool.false_eq_true,ite_false,ite_true,hasRoyal,transport_number]

/-- Summary sufficiency holds separately for the independently defined C_r/C_nr. -/
def stratumIso (r : Bool) (u v : Board)
    (hu : OnlyConfined u) (hv : OnlyConfined v)
    (hu1 : I1 u) (hu2 : I2 u) (hu3 : I3 u) (hv1 : I1 v) (hv2 : I2 v) (hv3 : I3 v)
    (he : boardSummary u = boardSummary v) :
    FiniteRelabelling.Iso {f : Board // StratumCompletes r u f} {f : Board // StratumCompletes r v f} := by
  let e := of_summary u v hu1 hv1 hu hv he
  have ht (f : Board) (h : StratumCompletes r u f) : StratumCompletes r v (transport e.toRelabelling f) := by
    obtain ⟨hc,hr⟩ := (stratum_iff r u f hu).mp h
    apply (stratum_iff r v _ hv).mpr
    exact ⟨transport_completion u v f hu hv hu1 hu2 hu3 hv1 hv2 hv3 he e hc,
      (transport_royalMode r u v f e).mpr hr⟩
  have hb (f : Board) (h : StratumCompletes r v f) : StratumCompletes r u (transport (inverse u v e).toRelabelling f) := by
    obtain ⟨hc,hr⟩ := (stratum_iff r v f hv).mp h
    apply (stratum_iff r u _ hu).mpr
    exact ⟨transport_completion v u f hv hu hv1 hv2 hv3 hu1 hu2 hu3 he.symm (inverse u v e) hc,
      (transport_royalMode r v u f (inverse u v e)).mpr hr⟩
  refine ⟨(fun f => ⟨transport e.toRelabelling f.val,ht f.val f.property⟩),
    (fun f => ⟨transport (inverse u v e).toRelabelling f.val,hb f.val f.property⟩),?_,?_⟩
  · intro f; apply Subtype.ext; exact Placement.transport_inverse e.toRelabelling f.val
  · intro f; apply Subtype.ext; exact Placement.inverse_transport e.toRelabelling f.val

end ChuShogi.SummarySufficiency
