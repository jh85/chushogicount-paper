import ChuShogi.CanonicalAlphabet
import ChuShogi.FiniteListEquivalence

/-! Explicit orderings of the actual present bishop/kirin bound labels. These
are canonical colour/class labels; original stock identities are not selected.
-/
namespace ChuShogi.CanonicalBoundLabels
open Promotion CanonicalAlphabet GroupConfigurations

def colours : List Colour := [.black,.white]
theorem colours_nodup : colours.Nodup := by decide
theorem colours_complete (c : Colour) : c ∈ colours := by cases c <;> simp [colours]

def bishops (g : Config r s) (a : Bool) : List (BishopLabel g a) :=
  FiniteListEquivalence.subtypeEntries colours (fun c => bishopCount g a c=1)
def kirins (g : Config r s) : List (KirinLabel g) :=
  FiniteListEquivalence.subtypeEntries colours (fun c => (g.kirin c).val.1=1)

theorem bishops_nodup (g : Config r s) (a : Bool) : (bishops g a).Nodup :=
  FiniteListEquivalence.subtypeEntries_nodup _ colours_nodup _
theorem kirins_nodup (g : Config r s) : (kirins g).Nodup :=
  FiniteListEquivalence.subtypeEntries_nodup _ colours_nodup _
theorem bishops_complete (g : Config r s) (a : Bool) (c : BishopLabel g a) : c ∈ bishops g a :=
  FiniteListEquivalence.subtypeEntries_complete _ colours_complete _ c
theorem kirins_complete (g : Config r s) (c : KirinLabel g) : c ∈ kirins g :=
  FiniteListEquivalence.subtypeEntries_complete _ colours_complete _ c

def bishopListEquivalence (g : Config r s) (a : Bool) : Fin (bishops g a).length ≃ BishopLabel g a :=
  FiniteListEquivalence.equivalence _ (bishops_nodup g a) (bishops_complete g a)
def kirinListEquivalence (g : Config r s) : Fin (kirins g).length ≃ KirinLabel g :=
  FiniteListEquivalence.equivalence _ (kirins_nodup g) (kirins_complete g)

def bishopNumber (g : Config r s) (a : Bool) : Nat := bishopCount g a .black+bishopCount g a .white
def kirinNumber (g : Config r s) : Nat := (g.kirin .black).val.1+(g.kirin .white).val.1

theorem bishops_length (g : Config r s) (a : Bool) : (bishops g a).length=bishopNumber g a := by
  have h := Fintype.card_congr (bishopListEquivalence g a)
  simpa only [Fintype.card_fin,bishop_card,bishopNumber] using h
theorem kirins_length (g : Config r s) : (kirins g).length=kirinNumber g := by
  have h := Fintype.card_congr (kirinListEquivalence g)
  simpa only [Fintype.card_fin,kirin_card,kirinNumber] using h

def bishopEquivalence (g : Config r s) (a : Bool) : Fin (bishopNumber g a) ≃ BishopLabel g a :=
  (finCongr (bishops_length g a).symm).trans (bishopListEquivalence g a)
def kirinEquivalence (g : Config r s) : Fin (kirinNumber g) ≃ KirinLabel g :=
  (finCongr (kirins_length g).symm).trans (kirinListEquivalence g)

def number0 (g : Config r s) : Nat := bishopNumber g false
def number1 (g : Config r s) : Nat := bishopNumber g true+kirinNumber g

def equivalence0 (g : Config r s) : Fin (number0 g) ≃ Bound0 g := bishopEquivalence g false
def equivalence1 (g : Config r s) : Fin (number1 g) ≃ Bound1 g :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (bishopEquivalence g true) (kirinEquivalence g))

theorem card0 (g : Config r s) : Fintype.card (Bound0 g)=number0 g := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (equivalence0 g)).symm
theorem card1 (g : Config r s) : Fintype.card (Bound1 g)=number1 g := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (equivalence1 g)).symm

end ChuShogi.CanonicalBoundLabels
