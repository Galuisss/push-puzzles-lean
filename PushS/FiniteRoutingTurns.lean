/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingSegments
public import PushS.FiniteTurn

/-! Actual owned concave-turn pieces and their oriented placements at route corners. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction FiniteGeometry

def rightTurn : Direction → Direction
  | .north => .east
  | .east => .south
  | .south => .west
  | .west => .north

def Perpendicular (d e : Direction) : Prop := e = rightTurn d ∨ e = (rightTurn d).opposite

/-- The standard right turn has its wall on the path's left. -/
def turnSide (d e : Direction) : Bool := decide (e = rightTurn d)

namespace Turn

open FiniteTools

attribute [local irreducible] FiniteTools.side

def label (i : Fin 2) : TurnLabel := if i = 0 then .horizontal else .vertical

def cell (w : ℕ) (q : Bool) (i : Fin 2) : Cell (FiniteTools.side w) (FiniteTools.side w) :=
  turnMixedCell w q q (label i)

theorem cell_injective (w : ℕ) (q : Bool) : Function.Injective (cell w q) := by
  intro a b he
  have hh := turnMixedCell_injective w q q he
  fin_cases a <;> fin_cases b <;> simp_all [cell, label]

def boxes (w : ℕ) (q : Bool) : Finset (Cell (FiniteTools.side w) (FiniteTools.side w)) := Finset.univ.image (cell w q)

private theorem cell_floor (w : ℕ) (q : Bool) (i : Fin 2) : cell w q i ∉ turnWalls w :=
  turnActive_floor w (turnMixedCell_active w q q (label i))

theorem boxes_floor (w : ℕ) (q : Bool) : Disjoint (boxes w q) (turnWalls w) := by
  apply Finset.disjoint_left.mpr
  intro p hp
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
  exact cell_floor w q i

theorem boxes_card (w : ℕ) (q : Bool) : (boxes w q).card = 2 := by
  rw [boxes, Finset.card_image_of_injective _ (cell_injective w q)]
  simp

def hub (w : ℕ) : Cell (FiniteTools.side w) (FiniteTools.side w) :=
  (⟨0, by unfold FiniteTools.side radius; omega⟩, ⟨0, by unfold FiniteTools.side radius; omega⟩)

theorem hub_floor (w : ℕ) : hub w ∉ turnWalls w := by
  intro hp
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
  have hh := ((turnRectangle w i).mem_cells _ _ _).mp hi
  fin_cases i
  · simp [turnRectangle, hub, radius] at hh
    omega
  · simp [turnRectangle, hub, radius] at hh

theorem hub_empty (w : ℕ) (q : Bool) : hub w ∉ boxes w q := by
  intro hp
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hp
  have hy := congrArg (fun p : Cell (FiniteTools.side w) (FiniteTools.side w) => p.2.val) hi
  have hq := Bool.toNat_le q
  fin_cases i <;> simp [cell, label, turnMixedCell, turnMixedPoint, hub, radius] at hy

/-- The turn owns exactly F and G; prepared neighboring boxes belong to adjacent straight pieces. -/
def puzzle (w : ℕ) (initial target : Bool) : PushFS.Instance where
  width := FiniteTools.side w
  height := FiniteTools.side w
  board := ⟨turnWalls w,boxes w target⟩
  initial := ⟨hub w,boxes w initial⟩
  goals_floor := (boxes_floor w target).symm
  initial_valid := ⟨hub_floor w,boxes_floor w initial,hub_empty w initial⟩
  boxes_eq_goals := (boxes_card w initial).trans (boxes_card w target).symm

def quarter (w : ℕ) : Direction → GridIsometry (FiniteTools.side w) (FiniteTools.side w) (FiniteTools.side w) (FiniteTools.side w)
  | .east => GridIsometry.refl _ _
  | .south => GridIsometry.clockwise _ _
  | .west => (GridIsometry.reflectX _ _).trans (GridIsometry.reflectY _ _)
  | .north => (GridIsometry.clockwise _ _).symm

/-- Right and left turns use the same concrete concave primitive with its appropriate reflection. -/
def orientation (w : ℕ) (incoming outgoing : Direction) :
    GridIsometry (FiniteTools.side w) (FiniteTools.side w) (FiniteTools.side w) (FiniteTools.side w) :=
  (if outgoing = rightTurn incoming then GridIsometry.refl _ _ else GridIsometry.reflectY _ _).trans
    (quarter w incoming)

def center (w : ℕ) : Cell (FiniteTools.side w) (FiniteTools.side w) := turnNode w .corner

private theorem quarter_center (w : ℕ) (d : Direction) : (quarter w d).cells
    (center w) = center w := by
  cases d
  · apply Prod.ext <;> apply Fin.ext
    · rfl
    · change FiniteTools.side w-(radius w+1) = radius w
      unfold FiniteTools.side
      omega
  · rfl
  · apply Prod.ext <;> apply Fin.ext
    · change FiniteTools.side w-(radius w+1) = radius w
      unfold FiniteTools.side
      omega
    · rfl
  · apply Prod.ext <;> apply Fin.ext <;>
      change FiniteTools.side w-(radius w+1) = radius w <;> unfold FiniteTools.side <;> omega

private theorem reflect_center (w : ℕ) : (GridIsometry.reflectY (FiniteTools.side w)
    (FiniteTools.side w)).cells (center w) = center w := by
  apply Prod.ext <;> apply Fin.ext
  · rfl
  · change FiniteTools.side w-(radius w+1) = radius w
    unfold FiniteTools.side
    omega

theorem orientation_center (w : ℕ) (d e : Direction) :
    (orientation w d e).cells (center w) = center w := by
  unfold orientation
  split_ifs
  · exact quarter_center w d
  · change (quarter w d).cells ((GridIsometry.reflectY _ _).cells (center w)) = center w
    rw [reflect_center]
    exact quarter_center w d

def offsetX (w : ℕ) (p : ℕ × ℕ) : ℕ := padding w+p.1-radius w

def offsetY (w : ℕ) (p : ℕ × ℕ) : ℕ := padding w+p.2-radius w

theorem fits (w : ℕ) (p : ℕ × ℕ) (hp : p.1 ≤ tileStride w ∧ p.2 ≤ tileStride w) :
    offsetX w p+FiniteTools.side w ≤ tileSide w ∧ offsetY w p+FiniteTools.side w ≤ tileSide w := by
  unfold offsetX offsetY FiniteTools.side radius tileSide padding
  omega

def placement (w : ℕ) (d e : Direction) (p : ℕ × ℕ)
    (hp : p.1 ≤ tileStride w ∧ p.2 ≤ tileStride w) :
    GridEmbedding (FiniteTools.side w) (FiniteTools.side w) (tileSide w) (tileSide w) :=
  (orientation w d e).embedding.trans
    (GridEmbedding.translate (offsetX w p) (offsetY w p) (fits w p hp).1 (fits w p hp).2)

def orientedPuzzle (w : ℕ) (d e : Direction) (initial target : Bool) : PushFS.Instance :=
  GridIsometry.reorientInstance (puzzle w initial target) (orientation w d e)

def patch (w : ℕ) (d e : Direction) (p : ℕ × ℕ) (initial target : Bool) : Bitmap.Patch :=
  Bitmap.instancePatch (orientedPuzzle w d e initial target) (offsetX w p) (offsetY w p)

theorem patch_fits (w : ℕ) (d e : Direction) (p : ℕ × ℕ) (initial target : Bool)
    (hp : p.1 ≤ tileStride w ∧ p.2 ≤ tileStride w) :
    (patch w d e p initial target).x+(patch w d e p initial target).bitmap.width ≤ tileSide w ∧
      (patch w d e p initial target).y+(patch w d e p initial target).bitmap.height ≤ tileSide w := fits w p hp

end Turn
end PushPuzzle.PushS.FiniteRouting
