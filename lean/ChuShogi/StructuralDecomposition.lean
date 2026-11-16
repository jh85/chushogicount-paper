import ChuShogi.TupleRendering

/-! Full unique decomposition of independently defined Candidate Boards into a
valid local tuple and an actual stratum completion. No origin witnesses occur. -/
namespace ChuShogi.StructuralDecomposition
open Specification Promotion ConcreteDP BoardDecomposition SummaryBridge Rendering
open TupleRendering Completion SummarySufficiency

def Stratum (r : Bool) (b : Board) : Prop := if r then C_r b else C_nr b

theorem stratum_candidate (r : Bool) (b : Board) (h : Stratum r b) : Candidate b := by
  cases r <;> exact h.1

noncomputable def renderAny (us : List Local) : Board := by
  classical
  exact if h : ConcreteDP.Valid us then renderTuple us h else fun _ => none

theorem renderAny_eq (us : List Local) (h : ConcreteDP.Valid us) : renderAny us = renderTuple us h := by
  simp only [renderAny,dite_eq_left h]

theorem renderAny_valid (us : List Local) (h : ConcreteDP.Valid us) :
    OnlyConfined (renderAny us) ∧ I1 (renderAny us) ∧ I2 (renderAny us) ∧ I3 (renderAny us) := by
  rw [renderAny_eq us h]
  exact (tupleBoardIso.forward ⟨us,h⟩).property

theorem boardTuple_renderAny (us : List Local) (h : ConcreteDP.Valid us) :
    boardTuple (renderAny us) = us := by rw [renderAny_eq us h]; exact boardTuple_renderTuple us h

theorem renderAny_projection (b : Board) (hc : OnlyConfined b) (h1 : I1 b) (h2 : I2 b) (h3 : I3 b) :
    renderAny (boardTuple b) = b := by
  rw [renderAny_eq _ (boardTuple_valid b h1 h2 h3)]
  exact congrArg Subtype.val (tupleBoardIso.right_inverse ⟨b,hc,h1,h2,h3⟩)

abbrev Parts := List Local × Board

def ValidParts (r : Bool) (p : Parts) : Prop :=
  ConcreteDP.Valid p.1 ∧ StratumCompletes r (renderAny p.1) p.2

noncomputable def assemble (p : Parts) : Board := merge (renderAny p.1) p.2

def decompose (b : Board) : Parts := (boardTuple (confined b),free b)

theorem assemble_sound (r : Bool) (p : Parts) (h : ValidParts r p) : Stratum r (assemble p) := h.2.2.2

theorem decompose_valid (r : Bool) (b : Board) (h : Stratum r b) : ValidParts r (decompose b) := by
  have hc := stratum_candidate r b h
  have h1 := (confined_I1 b).mpr hc.1
  have h2 := (confined_I2 b).mpr hc.2.1
  have h3 := (confined_I3 b).mpr hc.2.2.1
  have hs := split_properties b
  refine ⟨boardTuple_valid _ h1 h2 h3,?_⟩
  change StratumCompletes r (renderAny (boardTuple (confined b))) (free b)
  rw [renderAny_projection _ hs.1 h1 h2 h3]
  exact ⟨hs.2.1,hs.2.2,by rw [merge_split]; exact h⟩

theorem assemble_decompose (r : Bool) (b : Board) (h : Stratum r b) : assemble (decompose b) = b := by
  have hc := stratum_candidate r b h
  unfold assemble decompose
  rw [renderAny_projection _ (split_properties b).1 ((confined_I1 b).mpr hc.1)
    ((confined_I2 b).mpr hc.2.1) ((confined_I3 b).mpr hc.2.2.1),merge_split]

theorem decompose_assemble (r : Bool) (p : Parts) (h : ValidParts r p) : decompose (assemble p) = p := by
  have hu := renderAny_valid p.1 h.1
  have hs := split_merge (renderAny p.1) p.2 hu.1 h.2.1 h.2.2.1
  apply Prod.ext
  · change boardTuple (confined (merge (renderAny p.1) p.2)) = p.1
    rw [hs.1,boardTuple_renderAny p.1 h.1]
  · exact hs.2

/-- Sound, complete, and free from duplicate Board counting, for both C_r and C_nr. -/
noncomputable def decompositionIso (r : Bool) :
    FiniteRelabelling.Iso {p : Parts // ValidParts r p} {b : Board // Stratum r b} where
  forward p := ⟨assemble p.val,assemble_sound r p.val p.property⟩
  backward b := ⟨decompose b.val,decompose_valid r b.val b.property⟩
  left_inverse p := by apply Subtype.ext; exact decompose_assemble r p.val p.property
  right_inverse b := by apply Subtype.ext; exact assemble_decompose r b.val b.property

end ChuShogi.StructuralDecomposition
