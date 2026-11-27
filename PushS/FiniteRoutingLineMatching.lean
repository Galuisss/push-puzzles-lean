/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineBoard
public import PushFS.StaticLine
public import PushFS.StaticTracks

/-! Complete static slot matchings and endpoint ownership for emitted straight pieces. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line

open PushFS FiniteGeometry

attribute [local irreducible] width height

private def rowLine (w : ℕ) (atoms : List Atom) (i : Fin (span w atoms+4)) :
    Cell (width w atoms) (height w) :=
  (⟨FiniteTools.radius w-1+i.val, by unfold width FiniteTools.radius at *; omega⟩,
   ⟨FiniteTools.radius w, by unfold height FiniteTools.side; omega⟩)

private def slotIndex (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (q : Bool) (l : Label w atoms) :
    Fin (span w atoms+4) :=
  ⟨position w atoms q l+1, by
    have hb := positions_bounds w hw q atoms (position_mem w atoms q l)
    have hq := Bool.toNat_le q
    omega⟩

private theorem rowLine_slot (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (q : Bool) (l : Label w atoms) :
    rowLine w atoms (slotIndex w hw atoms q l) = cell w hw atoms q l := by
  apply Prod.ext <;> apply Fin.ext
  · change FiniteTools.radius w-1+(position w atoms q l+1) = FiniteTools.radius w+position w atoms q l
    unfold FiniteTools.radius
    omega
  · rfl

/-- Every owned line and auxiliary box has its two actual normal positions in one wall-only SCC. -/
theorem cell_connected (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (above q q' : Bool)
    (goals : Finset (Cell (width w atoms) (height w))) (l : Label w atoms) :
    SameComponent (⟨walls w atoms above,goals⟩ : Board (width w atoms) (height w))
      (cell w hw atoms q l) (cell w hw atoms q' l) := by
  have hh := sameComponent_line (n := span w atoms+1) (d := .east)
    (B := (⟨walls w atoms above,goals⟩ : Board (width w atoms) (height w)))
    (rowLine w atoms)
    (fun i => row_floor w atoms above _ rfl)
    (by intro i; dsimp [Adjacent, rowLine]; exact ⟨by omega,rfl⟩)
    (slotIndex w hw atoms q l) (slotIndex w hw atoms q' l)
    (by
      have hb := positions_bounds w hw q atoms (position_mem w atoms q l)
      have hq := Bool.toNat_le q
      dsimp [slotIndex]
      omega)
    (by
      have hb := positions_bounds w hw q' atoms (position_mem w atoms q' l)
      have hq := Bool.toNat_le q'
      dsimp [slotIndex]
      omega)
  simpa only [rowLine_slot] using hh

/-- Boundary ownership can retain either shared endpoint independently. -/
abbrev OwnedLabel (w : ℕ) (atoms : List Atom) (first last : Bool) :=
  {l : Label w atoms // (first = true ∨ 0 < l.val) ∧
    (last = true ∨ l.val+1 < (positions w false atoms).length)}

def ownedCell (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (first last phase : Bool)
    (l : OwnedLabel w atoms first last) : Cell (width w atoms) (height w) := cell w hw atoms phase l.val

theorem ownedCell_injective (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (first last phase : Bool) :
    Function.Injective (ownedCell w hw atoms first last phase) := by
  intro a b he
  exact Subtype.ext (cell_injective w hw atoms phase he)

def ownedBoxes (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (first last phase : Bool) :
    Finset (Cell (width w atoms) (height w)) := Finset.univ.image (ownedCell w hw atoms first last phase)

theorem ownedBoxes_disjoint_walls (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (above first last phase : Bool) :
    Disjoint (ownedBoxes w hw atoms first last phase) (walls w atoms above) := by
  apply Finset.disjoint_left.mpr
  intro p hp
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
  exact row_floor w atoms above _ rfl

theorem ownedBoxes_card (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (first last phase : Bool) :
    (ownedBoxes w hw atoms first last phase).card = Fintype.card (OwnedLabel w atoms first last) := by
  rw [ownedBoxes, Finset.card_image_of_injective _ (ownedCell_injective w hw atoms first last phase)]
  exact Finset.card_univ

def ownedPuzzle (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (above first last initial target : Bool) : PushFS.Instance where
  width := width w atoms
  height := height w
  board := ⟨walls w atoms above, ownedBoxes w hw atoms first last target⟩
  initial := ⟨hub w atoms, ownedBoxes w hw atoms first last initial⟩
  goals_floor := (ownedBoxes_disjoint_walls w hw atoms above first last target).symm
  initial_valid := ⟨hub_not_wall w atoms above, ownedBoxes_disjoint_walls w hw atoms above first last initial, by
    intro hp
    obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hp
    exact hub_not_box w hw atoms initial (Finset.mem_image.mpr ⟨l.val,Finset.mem_univ _,hl⟩)⟩
  boxes_eq_goals := (ownedBoxes_card w hw atoms first last initial).trans
    (ownedBoxes_card w hw atoms first last target).symm

def ownedMatching (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (above first last initial target : Bool) :
    SlotMatching (ownedPuzzle w hw atoms above first last initial target) (OwnedLabel w atoms first last) where
  source := ⟨ownedCell w hw atoms first last initial, ownedCell_injective w hw atoms first last initial⟩
  target := ⟨ownedCell w hw atoms first last target, ownedCell_injective w hw atoms first last target⟩
  source_image := by ext p; simp [ownedPuzzle, ownedBoxes, Finset.map_eq_image]
  target_image := by ext p; simp [ownedPuzzle, ownedBoxes, Finset.map_eq_image]
  connected l := cell_connected w hw atoms above initial target _ l.val

end PushPuzzle.PushS.FiniteRouting.Line
