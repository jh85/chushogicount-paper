import ChuShogi.WeightedDP

/-!
Class-preserving relabelling of free placements. `Allowed` describes the role
constraint on a square class independently of any enumeration. This is the
combinatorial part of summary sufficiency; occupancy and capacity summaries
must still be related to the whole-Board specification.
-/
namespace ChuShogi.Placement

variable {Square Role Class : Type}

/-- A permutation between two residual square sets, preserving square class. -/
structure Relabelling (class₁ : Square → Class) (class₂ : Square → Class) where
  forward : Square → Square
  backward : Square → Square
  left_inverse : ∀ s, backward (forward s) = s
  right_inverse : ∀ s, forward (backward s) = s
  preserves_class : ∀ s, class₂ (forward s) = class₁ s

/-- Free placements are maps, hence identical pieces have no origin labels. -/
abbrev FreePlacement (Square Role : Type) := Square → Option Role

def transport {class₁ class₂ : Square → Class}
    (e : Relabelling class₁ class₂) (b : FreePlacement Square Role) : FreePlacement Square Role :=
  fun s => b (e.backward s)

def inverseTransport {class₁ class₂ : Square → Class}
    (e : Relabelling class₁ class₂) (b : FreePlacement Square Role) : FreePlacement Square Role :=
  fun s => b (e.forward s)

theorem transport_inverse {class₁ class₂ : Square → Class}
    (e : Relabelling class₁ class₂) (b : FreePlacement Square Role) :
    inverseTransport e (transport e b) = b := by
  funext s
  simp only [inverseTransport, transport, e.left_inverse]

theorem inverse_transport {class₁ class₂ : Square → Class}
    (e : Relabelling class₁ class₂) (b : FreePlacement Square Role) :
    transport e (inverseTransport e b) = b := by
  funext s
  simp only [inverseTransport, transport, e.right_inverse]

/-- Local colour restrictions plus an independent global multiset predicate. -/
def ValidFree (classOf : Square → Class) (Allowed : Class → Role → Prop)
    (Material : FreePlacement Square Role → Prop) (b : FreePlacement Square Role) : Prop :=
  (∀ s r, b s = some r → Allowed (classOf s) r) ∧ Material b

/-- A bijection of completion sets once the material predicate is invariant. -/
theorem valid_transport_iff {class₁ class₂ : Square → Class}
    (e : Relabelling class₁ class₂) (Allowed : Class → Role → Prop)
    (Material₁ Material₂ : FreePlacement Square Role → Prop)
    (hm : ∀ b, Material₂ (transport e b) ↔ Material₁ b) (b : FreePlacement Square Role) :
    ValidFree class₂ Allowed Material₂ (transport e b) ↔
      ValidFree class₁ Allowed Material₁ b := by
  unfold ValidFree
  rw [hm]
  constructor
  · rintro ⟨h, hm⟩
    refine ⟨?_, hm⟩
    intro s r hr
    have ht : transport e b (e.forward s) = some r := by
      simpa only [transport, e.left_inverse] using hr
    have ha := h (e.forward s) r ht
    simpa only [e.preserves_class] using ha
  · rintro ⟨h, hm⟩
    refine ⟨?_, hm⟩
    intro s r hr
    have ha := h (e.backward s) r hr
    have hc := e.preserves_class (e.backward s)
    rw [e.right_inverse] at hc
    rwa [← hc] at ha

/-- Finite square lists related by relabelling give the same piece counts. -/
def multiplicity [DecidableEq Role] (squares : List Square)
    (b : FreePlacement Square Role) (r : Role) : Nat :=
  (squares.filter fun s => decide (b s = some r)).length

theorem multiplicity_transport [DecidableEq Role] {class₁ class₂ : Square → Class}
    (e : Relabelling class₁ class₂) (squares : List Square)
    (b : FreePlacement Square Role) (r : Role) :
    multiplicity (squares.map e.forward) (transport e b) r = multiplicity squares b r := by
  induction squares with
  | nil => rfl
  | cons s ss ih =>
    simp only [multiplicity, List.map_cons, List.filter_cons, transport, e.left_inverse]
    split <;> simp_all [multiplicity, transport]

/-- Multiplicity per square colour class, sufficient for bishops as well as material. -/
def classMultiplicity [DecidableEq Role] [DecidableEq Class]
    (squares : List Square) (classOf : Square → Class)
    (b : FreePlacement Square Role) (a : Class) (r : Role) : Nat :=
  (squares.filter fun s => decide (classOf s = a ∧ b s = some r)).length

theorem classMultiplicity_transport [DecidableEq Role] [DecidableEq Class]
    {class₁ class₂ : Square → Class} (e : Relabelling class₁ class₂)
    (squares : List Square) (b : FreePlacement Square Role) (a : Class) (r : Role) :
    classMultiplicity (squares.map e.forward) class₂ (transport e b) a r =
      classMultiplicity squares class₁ b a r := by
  induction squares with
  | nil => rfl
  | cons s ss ih =>
    simp only [classMultiplicity, List.map_cons, List.filter_cons, transport,
      e.left_inverse, e.preserves_class]
    split <;> simp_all [classMultiplicity, transport]

/-- The material-invariance hypothesis is discharged for any condition on counts.
This includes canonical role bounds, royal requirements, promotion capacities,
and class-specific bishop bounds once the remaining-square bijection is given. -/
theorem valid_byCounts_transport [DecidableEq Role] [DecidableEq Class]
    {class₁ class₂ : Square → Class} (e : Relabelling class₁ class₂)
    (squares : List Square) (Allowed : Class → Role → Prop)
    (Material : (Role → Nat) → (Class → Role → Nat) → Prop)
    (b : FreePlacement Square Role) :
    ValidFree class₂ Allowed
      (fun c => Material (multiplicity (squares.map e.forward) c)
        (classMultiplicity (squares.map e.forward) class₂ c)) (transport e b) ↔
    ValidFree class₁ Allowed
      (fun c => Material (multiplicity squares c) (classMultiplicity squares class₁ c)) b := by
  apply valid_transport_iff
  intro c
  have hm : multiplicity (squares.map e.forward) (transport e c) = multiplicity squares c := by
    funext r; exact multiplicity_transport e squares c r
  have hc : classMultiplicity (squares.map e.forward) class₂ (transport e c) =
      classMultiplicity squares class₁ c := by
    funext a r; exact classMultiplicity_transport e squares c a r
  rw [hm,hc]

/-- A finite duplicate-free completion enumeration can be transported bijectively. -/
theorem transport_nodup {class₁ class₂ : Square → Class}
    (e : Relabelling class₁ class₂) (bs : List (FreePlacement Square Role)) (hn : bs.Nodup) :
    (bs.map (transport e)).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  apply List.Pairwise.imp _ hn
  intro b c hbc heq
  have he := congrArg (inverseTransport e) heq
  rw [transport_inverse, transport_inverse] at he
  exact hbc he

end ChuShogi.Placement
