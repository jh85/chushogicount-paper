import ChuShogi.ConcreteDP

/-! Canonical Board decomposition and recovery of confined slot ranks.
The components contain present pieces, not labels for their possible origins. -/
namespace ChuShogi.BoardDecomposition
open Specification Promotion

def isConfined : Role → Bool
  | .native .pawn | .native .lance | .native .chariot | .native .goBetween => true
  | _ => false

def confined (b : Board) : Board := fun s => (b s).filter (fun p => isConfined p.2)
def free (b : Board) : Board := fun s => (b s).filter (fun p => !isConfined p.2)
def merge (u f : Board) : Board := fun s => (u s).orElse (fun _ => f s)

def OnlyConfined (u : Board) : Prop := ∀ s p, u s = some p → isConfined p.2 = true
def OnlyFree (f : Board) : Prop := ∀ s p, f s = some p → isConfined p.2 = false
def Disjoint (u f : Board) : Prop := ∀ s, u s = none ∨ f s = none

theorem isConfined_kind (k : Kind) : isConfined (.native (kindBase k)) = true := by
  cases k <;> rfl

theorem isConfined_iff (r : Role) :
    isConfined r = true ↔ ∃ k, r = .native (kindBase k) := by
  cases r with
  | promoted p => simp [isConfined]
  | native b => cases b <;> simp [isConfined] <;>
      first | exact ⟨.pawn,rfl⟩ | exact ⟨.lance,rfl⟩ |
        exact ⟨.chariot,rfl⟩ | exact ⟨.goBetween,rfl⟩ |
        (intro k; cases k <;> simp [kindBase])

theorem split_properties (b : Board) :
    OnlyConfined (confined b) ∧ OnlyFree (free b) ∧ Disjoint (confined b) (free b) := by
  refine ⟨?_,?_,?_⟩
  · intro s p hp
    simpa [confined, Option.filter_eq_some_iff] using (Option.filter_eq_some_iff.mp hp).2
  · intro s p hp
    have h := (Option.filter_eq_some_iff.mp hp).2
    simpa using h
  · intro s
    cases h : b s with
    | none => simp [confined,free,h]
    | some p => cases hc : isConfined p.2 <;> simp [confined,free,h,hc]

theorem merge_split (b : Board) : merge (confined b) (free b) = b := by
  funext s
  cases h : b s with
  | none => simp [merge,confined,free,h]
  | some p => cases hc : isConfined p.2 <;> simp [merge,confined,free,h,hc]

theorem split_merge (u f : Board) (hu : OnlyConfined u) (hf : OnlyFree f) (hd : Disjoint u f) :
    confined (merge u f) = u ∧ free (merge u f) = f := by
  constructor <;> funext s
  all_goals
    cases hs : u s with
    | none =>
      cases ht : f s with
      | none => simp [confined,free,merge,hs,ht]
      | some p => simp [confined,free,merge,hs,ht,hf s p ht]
    | some p =>
      have ht : f s = none := (hd s).resolve_left (by simp [hs])
      simp [confined,free,merge,hs,ht,hu s p hs]

/-- No two canonical decompositions can give the same Board. -/
theorem decomposition_unique (u f u' f' : Board)
    (hu : OnlyConfined u) (hf : OnlyFree f) (hd : Disjoint u f)
    (hu' : OnlyConfined u') (hf' : OnlyFree f') (hd' : Disjoint u' f')
    (he : merge u f = merge u' f') : u = u' ∧ f = f' := by
  have h := split_merge u f hu hf hd
  have h' := split_merge u' f' hu' hf' hd'
  exact ⟨h.1.symm.trans ((congrArg confined he).trans h'.1),
    h.2.symm.trans ((congrArg free he).trans h'.2)⟩

theorem mem_squares (s : Square) : s ∈ squares := by
  rcases s with ⟨x,r⟩
  simp [squares]

def slotSquares (b : Board) (x : Fin 12) (c : Colour) (k : Kind) : List Square :=
  squares.filter fun s => decide (s.1 = x ∧ b s = some (c,.native (kindBase k)))

theorem slotSquares_length (b : Board) (x : Fin 12) (c : Colour) (k : Kind) :
    (slotSquares b x c k).length =
      countWhere b c (.native (kindBase k)) (fun s => decide (s.1 = x)) := by
  unfold slotSquares countWhere
  congr 1
  apply List.filter_congr
  intro s _
  simp [Bool.and_comm]

theorem singleton_of_short_mem {A : Type} (xs : List A) (h : xs.length ≤ 1)
    (a : A) (ha : a ∈ xs) : xs = [a] := by
  cases xs with
  | nil => simp at ha
  | cons b bs =>
    have hb : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst bs
    have he : a = b := by simpa using ha
    subst a
    rfl

/-- I1 makes the sum-based specification recover the unique present slot rank. -/
theorem unpromoted_at (b : Board) (h : I1 b) (s : Square) (c : Colour) (k : Kind)
    (hs : b s = some (c,.native (kindBase k))) : unpromoted b s.1 c k = rank s := by
  have hn : (slotSquares b s.1 c k).length ≤ 1 := by
    rw [slotSquares_length]; exact h.2 _ _ _
  have hm : s ∈ slotSquares b s.1 c k := by simp [slotSquares,mem_squares,hs]
  have he := singleton_of_short_mem _ hn s hm
  change ((slotSquares b s.1 c k).map rank).sum = _
  rw [he]
  simp

/-- A nonzero extracted rank comes from a present confined piece on that file. -/
theorem unpromoted_present (b : Board) (h : I1 b) (x : Fin 12) (c : Colour) (k : Kind)
    (hn : unpromoted b x c k ≠ 0) :
    ∃ s, s.1 = x ∧ b s = some (c,.native (kindBase k)) ∧ unpromoted b x c k = rank s := by
  have hl : slotSquares b x c k ≠ [] := by
    intro he
    apply hn
    change ((slotSquares b x c k).map rank).sum = 0
    simp [he]
  cases he : slotSquares b x c k with
  | nil => exact False.elim (hl he)
  | cons s tail =>
    have hm : s ∈ slotSquares b x c k := by rw [he]; simp
    have hs := (List.mem_filter.mp hm).2
    have hs' : s.1 = x ∧ b s = some (c,.native (kindBase k)) := of_decide_eq_true hs
    refine ⟨s,hs'.1,hs'.2,?_⟩
    rw [← hs'.1]
    exact unpromoted_at b h s c k hs'.2

/-- Exact recovery, rather than just recovery of a numeric sum. -/
theorem piece_iff_rank (b : Board) (h : I1 b) (s : Square) (c : Colour) (k : Kind) :
    b s = some (c,.native (kindBase k)) ↔ unpromoted b s.1 c k = rank s := by
  constructor
  · exact unpromoted_at b h s c k
  · intro he
    have hn : unpromoted b s.1 c k ≠ 0 := by rw [he]; unfold rank; omega
    obtain ⟨t,ht,hp,hr⟩ := unpromoted_present b h s.1 c k hn
    have htr : t.2 = s.2 := by
      apply Fin.ext
      have heq : rank t = rank s := hr.symm.trans he
      unfold rank at heq
      omega
    have hts : t = s := Prod.ext ht htr
    simpa [hts] using hp

/-- Present confined Boards cannot alias under the slot-rank projection. -/
theorem confined_projection_injective (b d : Board) (hb : I1 b) (hd : I1 d)
    (hbc : OnlyConfined b) (hdc : OnlyConfined d)
    (he : unpromoted b = unpromoted d) : b = d := by
  funext s
  cases hs : b s with
  | none =>
    cases ht : d s with
    | none => rfl
    | some p =>
      obtain ⟨k,hk⟩ := (isConfined_iff p.2).mp (hdc s p ht)
      have hp : d s = some (p.1,.native (kindBase k)) := by simpa [← hk] using ht
      have hr := (piece_iff_rank d hd s p.1 k).mp hp
      rw [← he] at hr
      have hc := (piece_iff_rank b hb s p.1 k).mpr hr
      simp [hs] at hc
  | some p =>
    obtain ⟨k,hk⟩ := (isConfined_iff p.2).mp (hbc s p hs)
    have hp : b s = some (p.1,.native (kindBase k)) := by simpa [← hk] using hs
    have hr := (piece_iff_rank b hb s p.1 k).mp hp
    rw [he] at hr
    have hc := (piece_iff_rank d hd s p.1 k).mpr hr
    simpa only [← hk] using hc.symm

open ConcreteDP

def boardLocal (b : Board) (x : Fin 12) : Local :=
  (x,(labels x).map fun l => unpromoted b x l.1 l.2)

theorem labels_membership (x : Fin 12) (c : Colour) (k : Kind) :
    (c,k) ∈ labels x ↔ HasSlot x c k := by
  cases c <;> cases k <;> revert x <;> decide

theorem labels_ordered (x : Fin 12) :
    (labels x).Pairwise (fun l m => confinedStart l.1 l.2 < confinedStart m.1 m.2) := by
  unfold labels
  split
  · decide
  · split <;> decide

theorem orderedLabel_black (c : Colour) (k : Kind) :
    orderedLabel (c,k) = .blackPawn ↔ c = .black ∧ k = .pawn := by
  cases c <;> cases k <;> decide

theorem orderedLabel_white (c : Colour) (k : Kind) :
    orderedLabel (c,k) = .whitePawn ↔ c = .white ∧ k = .pawn := by
  cases c <;> cases k <;> decide

theorem unpromoted_bound (b : Board) (h1 : I1 b) (h3 : I3 b)
    (x : Fin 12) (c : Colour) (k : Kind) :
    unpromoted b x c k = 0 ∨ OrderedFile.RankAllowed (orderedLabel (c,k)) (unpromoted b x c k) := by
  by_cases hz : unpromoted b x c k = 0
  · exact Or.inl hz
  · right
    obtain ⟨s,_,hs,hr⟩ := unpromoted_present b h1 x c k hz
    rw [hr]
    unfold OrderedFile.RankAllowed
    refine ⟨by unfold rank; omega, by unfold rank; omega, ?_, ?_⟩
    · intro hp
      obtain ⟨rfl,rfl⟩ := (orderedLabel_black c k).mp hp
      exact h3.1 s hs
    · intro hp
      obtain ⟨rfl,rfl⟩ := (orderedLabel_white c k).mp hp
      exact h3.2 s hs

theorem bounded_map (ls : List Label) (r : Label → Nat)
    (h : ∀ l ∈ ls, r l = 0 ∨ OrderedFile.RankAllowed (orderedLabel l) (r l)) :
    OrderedFile.Bounded (ls.map orderedLabel) (ls.map r) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    exact ⟨r l,ls.map r,rfl,h l (by simp),ih (fun a ha => h a (by simp [ha]))⟩

theorem ordered_pairwise (rs : List Nat) :
    OrderedFile.Ordered rs ↔ rs.Pairwise (fun r t => r = 0 ∨ t = 0 ∨ r < t) := by
  induction rs with
  | nil => simp [OrderedFile.Ordered]
  | cons r rs ih => simp only [OrderedFile.Ordered,List.pairwise_cons,ih]

/-- The independent Board conditions imply precisely admissible local records. -/
theorem boardLocal_admissible (b : Board) (h1 : I1 b) (h2 : I2 b) (h3 : I3 b) (x : Fin 12) :
    LocalAdmissible x (boardLocal b x) := by
  refine ⟨rfl,?_,?_⟩
  · exact bounded_map (labels x) _ (fun l _ => unpromoted_bound b h1 h3 x l.1 l.2)
  · change OrderedFile.Ordered ((labels x).map fun l => unpromoted b x l.1 l.2)
    rw [ordered_pairwise,List.pairwise_map]
    apply List.Pairwise.imp _ (labels_ordered x)
    intro l m hlm
    by_cases hl : unpromoted b x l.1 l.2 = 0
    · exact Or.inl hl
    by_cases hm : unpromoted b x m.1 m.2 = 0
    · exact Or.inr (Or.inl hm)
    obtain ⟨s,hs,hsp,hsr⟩ := unpromoted_present b h1 x l.1 l.2 hl
    obtain ⟨t,ht,htp,htr⟩ := unpromoted_present b h1 x m.1 m.2 hm
    exact Or.inr (Or.inr (by rw [hsr,htr]; exact h2 s t l.1 m.1 l.2 m.2 hsp htp (hs.trans ht.symm) hlm))

theorem confined_at_kind (b : Board) (s : Square) (c : Colour) (k : Kind) :
    confined b s = some (c,.native (kindBase k)) ↔ b s = some (c,.native (kindBase k)) := by
  simp [confined,Option.filter_eq_some_iff,isConfined_kind]

theorem confined_count_kind (b : Board) (c : Colour) (k : Kind) (p : Square → Bool) :
    countWhere (confined b) c (.native (kindBase k)) p = countWhere b c (.native (kindBase k)) p := by
  unfold countWhere
  simp only [confined_at_kind]

theorem confined_I1 (b : Board) : I1 (confined b) ↔ I1 b := by
  simp only [I1,confined_at_kind,confined_count_kind]

theorem confined_I2 (b : Board) : I2 (confined b) ↔ I2 b := by
  simp only [I2,confined_at_kind]

theorem confined_I3 (b : Board) : I3 (confined b) ↔ I3 b := by
  change ((∀ s, confined b s = some (.black,.native (kindBase .pawn)) → 4 ≤ rank s) ∧
    (∀ s, confined b s = some (.white,.native (kindBase .pawn)) → rank s ≤ 9)) ↔ _
  simp only [confined_at_kind]
  rfl

theorem unpromoted_confined (b : Board) : unpromoted (confined b) = unpromoted b := by
  funext x c k
  simp only [unpromoted,confined_at_kind]

def boardTuple (b : Board) : List Local := ConcreteDP.indices.map (boardLocal b)

theorem boardTuple_valid (b : Board) (h1 : I1 b) (h2 : I2 b) (h3 : I3 b) :
    ConcreteDP.Valid (boardTuple b) := by
  have general (xs : List (Fin 12)) :
      WeightedDP.Valid (xs.map LocalAdmissible) (xs.map (boardLocal b)) := by
    induction xs with
    | nil => rfl
    | cons x xs ih => exact ⟨boardLocal b x,xs.map (boardLocal b),rfl,
        boardLocal_admissible b h1 h2 h3 x,ih⟩
  exact general _

theorem candidate_tuple_mem (b : Board) (h : Candidate b) :
    boardTuple b ∈ WeightedDP.tuples ConcreteDP.files :=
  (WeightedDP.tuples_iff ConcreteDP.admissible ConcreteDP.files
    (ConcreteDP.enumerates _) _).mpr (boardTuple_valid b h.1 h.2.1 h.2.2.1)

theorem map_eq_on_mem {A B : Type} (xs : List A) (f g : A → B)
    (he : xs.map f = xs.map g) (a : A) (ha : a ∈ xs) : f a = g a := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    have hh := List.cons.inj he
    rcases List.mem_cons.mp ha with h | h
    · subst a; exact hh.1
    · exact ih hh.2 h

theorem absent_slot_zero (b : Board) (h1 : I1 b) (x : Fin 12) (c : Colour) (k : Kind)
    (hs : ¬ HasSlot x c k) : unpromoted b x c k = 0 := by
  by_cases hz : unpromoted b x c k = 0
  · exact hz
  · obtain ⟨s,hx,hp,_⟩ := unpromoted_present b h1 x c k hz
    exact False.elim (hs (by rw [← hx]; exact h1.1 s c k hp))

/-- Unique confined Boards map to unique admissible twelve-file tuples. -/
theorem boardTuple_injective (b d : Board) (hb : I1 b) (hd : I1 d)
    (hbc : OnlyConfined b) (hdc : OnlyConfined d) (he : boardTuple b = boardTuple d) : b = d := by
  apply confined_projection_injective b d hb hd hbc hdc
  funext x c k
  by_cases hs : HasSlot x c k
  · have hm : boardLocal b x ∈ boardTuple b := by
      apply List.mem_map.mpr
      exact ⟨x,by simp [ConcreteDP.indices],rfl⟩
    rw [he] at hm
    obtain ⟨y,_,hy⟩ := List.mem_map.mp hm
    have hyx : y = x := congrArg Prod.fst hy
    subst y
    have hr := congrArg Prod.snd hy
    exact (map_eq_on_mem (labels x) _ _ hr (c,k) ((labels_membership x c k).mpr hs)).symm
  · rw [absent_slot_zero b hb x c k hs,absent_slot_zero d hd x c k hs]

end ChuShogi.BoardDecomposition


