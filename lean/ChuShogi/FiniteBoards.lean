import ChuShogi.StructuralDecomposition

/-! A finite universe of canonical Boards, independently of candidate counting.
This universe is used symbolically to define cardinalities, never evaluated to
obtain the manuscript integers. -/
namespace ChuShogi.FiniteBoards
open Specification

variable {A : Type}

def functions (values : List A) : (n : Nat) → List (Fin n → A)
  | 0 => [fun i => Fin.elim0 i]
  | n+1 => values.flatMap fun a => (functions values n).map fun f => Fin.cases a f

theorem functions_iff (values : List A) (n : Nat) (f : Fin n → A) :
    f ∈ functions values n ↔ ∀ i, f i ∈ values := by
  induction n with
  | zero =>
    have he : f = fun i => Fin.elim0 i := by funext i; exact Fin.elim0 i
    constructor
    · intro _ i; exact Fin.elim0 i
    · intro _; simp [functions,he]
  | succ n ih =>
    simp only [functions,List.mem_flatMap,List.mem_map]
    constructor
    · rintro ⟨a,ha,g,hg,rfl⟩ i
      exact Fin.cases ha (fun j => (ih g).mp hg j) i
    · intro h
      refine ⟨f 0,h 0,(fun i => f i.succ),(ih _).mpr (fun i => h i.succ),?_⟩
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

theorem functions_nodup (values : List A) (hv : values.Nodup) (n : Nat) : (functions values n).Nodup := by
  induction n with
  | zero => simp [functions]
  | succ n ih =>
    simp only [functions,List.nodup_iff_pairwise_ne,List.pairwise_flatMap,List.pairwise_map]
    constructor
    · intro a _
      apply List.Pairwise.imp _ ih
      intro f g hfg he
      apply hfg
      funext i
      exact congrFun he i.succ
    · apply List.Pairwise.imp _ hv
      intro a b hab f hf g hg he
      obtain ⟨f',_,rfl⟩ := List.mem_map.mp hf
      obtain ⟨g',_,rfl⟩ := List.mem_map.mp hg
      exact hab (congrFun he 0)

def bases : List Base :=
  [.pawn,.lance,.chariot,.goBetween,.gold,.silver,.copper,.leopard,.tiger,
   .sideMover,.verticalMover,.rook,.dragonHorse,.dragonKing,.bishop,
   .elephant,.kirin,.phoenix,.king,.lion,.freeKing]

def separate : List Separate :=
  [.pawn,.lance,.chariot,.goBetween,.gold,.silver,.copper,.leopard,.tiger,
   .sideMover,.verticalMover,.rook,.dragonHorse,.dragonKing,.bishop]

def roles : List Role := bases.map .native ++ separate.map .promoted

def options : List (Option Piece) := none ::
  [Promotion.Colour.black,Promotion.Colour.white].flatMap fun c => roles.map fun r => some (c,r)

set_option maxRecDepth 4096

theorem options_nodup : options.Nodup := by decide

theorem options_complete (p : Option Piece) : p ∈ options := by
  cases p with
  | none => decide
  | some p =>
    rcases p with ⟨c,r⟩
    cases c <;> cases r with
    | native b => cases b <;> decide
    | promoted b => cases b <;> decide

def squareIndex (s : Square) : Fin 144 := ⟨12*s.1.val+s.2.val,by omega⟩
def indexSquare (i : Fin 144) : Square := (⟨i.val/12,by omega⟩,⟨i.val%12,by omega⟩)

theorem square_index (s : Square) : indexSquare (squareIndex s) = s := by
  apply Prod.ext <;> apply Fin.ext <;> dsimp [indexSquare,squareIndex] <;> omega

theorem index_square (i : Fin 144) : squareIndex (indexSquare i) = i := by
  apply Fin.ext
  dsimp [indexSquare,squareIndex]
  omega

def toBoard (f : Fin 144 → Option Piece) : Board := fun s => f (squareIndex s)
def fromBoard (b : Board) : Fin 144 → Option Piece := fun i => b (indexSquare i)

theorem to_from (b : Board) : toBoard (fromBoard b) = b := by
  funext s
  simp only [toBoard,fromBoard,square_index]

theorem from_to (f : Fin 144 → Option Piece) : fromBoard (toBoard f) = f := by
  funext i
  simp only [toBoard,fromBoard,index_square]

def allBoards : List Board := (functions options 144).map toBoard

theorem universe_complete (b : Board) : b ∈ allBoards := by
  exact List.mem_map.mpr ⟨fromBoard b,(functions_iff _ _ _).mpr (fun _ => options_complete _),to_from b⟩

theorem universe_nodup : allBoards.Nodup := by
  rw [allBoards,List.nodup_iff_pairwise_ne,List.pairwise_map]
  apply List.Pairwise.imp _ (functions_nodup _ options_nodup 144)
  intro f g hfg he
  have hh := congrArg fromBoard he
  rw [from_to,from_to] at hh
  exact hfg hh

/-- Enumeration of any finite subtype, using a complete ambient list. -/
noncomputable def subtypeEnum {B : Type} (all : List B) (P : B → Prop) : List {b // P b} := by
  classical
  exact (all.filter fun b => decide (P b)).attach.map fun b =>
    (⟨b.val,by
      have hm := b.property
      simp only [List.mem_filter,decide_eq_true_eq] at hm
      exact hm.2⟩ : {b // P b})

theorem subtypeEnum_length {B : Type} (all : List B) (P : B → Prop) :
    (subtypeEnum all P).length = (all.filter fun b => @decide (P b) (Classical.propDecidable _)).length := by
  classical
  simp [subtypeEnum]

theorem subtypeEnum_complete {B : Type} (all : List B) (hc : ∀ b, b ∈ all) (P : B → Prop)
    (b : {b // P b}) : b ∈ subtypeEnum all P := by
  classical
  unfold subtypeEnum
  apply List.mem_map.mpr
  have hm : b.val ∈ all.filter (fun b => decide (P b)) := by simp [hc,b.property]
  exact ⟨⟨b.val,hm⟩,by simp,rfl⟩

theorem subtypeEnum_nodup {B : Type} (all : List B) (hn : all.Nodup) (P : B → Prop) :
    (subtypeEnum all P).Nodup := by
  classical
  rw [subtypeEnum,List.nodup_iff_pairwise_ne,List.pairwise_map]
  have hh : (((all.filter fun b => decide (P b)).attach).map Subtype.val).Nodup := by
    rw [List.attach_map_subtype_val]
    exact hn.filter _
  change (((all.filter fun b => decide (P b)).attach).map Subtype.val).Pairwise _ at hh
  rw [List.pairwise_map] at hh
  apply List.Pairwise.imp _ hh
  intro b c hbc he
  exact hbc (congrArg (fun b : {b // P b} => b.val) he)

/-- Cardinality via a duplicate-free complete universe, independent of the DP. -/
noncomputable def card (P : Board → Prop) : Nat := (subtypeEnum allBoards P).length

theorem subtypeEnum_complete_of {B : Type} (all : List B) (P : B → Prop)
    (hc : ∀ b, P b → b ∈ all) (b : {b // P b}) : b ∈ subtypeEnum all P := by
  classical
  unfold subtypeEnum
  apply List.mem_map.mpr
  have hm : b.val ∈ all.filter (fun b => decide (P b)) := by simp [hc b.val b.property,b.property]
  exact ⟨⟨b.val,hm⟩,by simp,rfl⟩

theorem subtypeEnum_length_of {B : Type} (all : List B) (P : B → Prop)
    (h : ∀ b ∈ all, P b) : (subtypeEnum all P).length = all.length := by
  classical
  unfold subtypeEnum
  simp only [List.length_map,List.length_attach]
  have he : (all.filter fun b => decide (P b)) = all := by
    apply List.filter_eq_self.mpr
    intro b hb
    exact decide_eq_true (h b hb)
  rw [he]

theorem iso_lengths {B C : Type} (xs : List B) (ys : List C)
    (hx : xs.Nodup) (hy : ys.Nodup) (hcx : ∀ b, b ∈ xs) (hcy : ∀ c, c ∈ ys)
    (e : FiniteRelabelling.Iso B C) : xs.length = ys.length := by
  have bound {D E : Type} (ls : List D) (rs : List E) (hn : ls.Nodup) (hc : ∀ e, e ∈ rs)
      (f : D → E) (g : E → D) (hi : ∀ d, g (f d) = d) : ls.length ≤ rs.length := by
    have hm : (ls.map f).Nodup := by
      rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
      apply List.Pairwise.imp _ hn
      intro a b hab he
      apply hab
      have hh := congrArg g he
      rwa [hi,hi] at hh
    have hh := hm.length_le_of_subset (fun _ _ => hc _)
    simpa using hh
  exact Nat.le_antisymm (bound xs ys hx hcy e.forward e.backward e.left_inverse)
    (bound ys xs hy hcx e.backward e.forward e.right_inverse)

theorem card_iso (P Q : Board → Prop) (e : FiniteRelabelling.Iso {b // P b} {b // Q b}) : card P = card Q :=
  iso_lengths _ _ (subtypeEnum_nodup allBoards universe_nodup P)
    (subtypeEnum_nodup allBoards universe_nodup Q)
    (subtypeEnum_complete allBoards universe_complete P)
    (subtypeEnum_complete allBoards universe_complete Q) e

end ChuShogi.FiniteBoards

