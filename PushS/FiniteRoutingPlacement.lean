/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingComplete
public import PushS.FiniteRoutingLineMatching
public import PushFS.Isometry

/-! Exact oriented placements of emitted straight pieces inside a common source macrocell. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

/-- A common collar contains full tool windows around boundary ports. -/
def padding (w : ℕ) : ℕ := 10*(w+3)

def tileStride (w : ℕ) : ℕ := 50*spacing w

def tileSide (w : ℕ) : ℕ := tileStride w+2*padding w+1

/-- Exact directed endpoint equations for a unit-box straight line. -/
def Travels (d : Direction) (p q : ℕ × ℕ) (length : ℕ) : Prop :=
  match d with
  | .north => p.1 = q.1 ∧ p.2 = q.2+length
  | .east => p.2 = q.2 ∧ q.1 = p.1+length
  | .south => p.1 = q.1 ∧ q.2 = p.2+length
  | .west => p.2 = q.2 ∧ p.1 = q.1+length

namespace Line

attribute [local irreducible] width height

def orientedWidth (w : ℕ) (atoms : List Atom) : Direction → ℕ
  | .east | .west => width w atoms
  | .north | .south => height w

def orientedHeight (w : ℕ) (atoms : List Atom) : Direction → ℕ
  | .east | .west => height w
  | .north | .south => width w atoms

/-- Proper rotations preserve the meaning of the above/left wall-side bit. -/
def rotation (w : ℕ) (atoms : List Atom) (d : Direction) :
    GridIsometry (width w atoms) (height w) (orientedWidth w atoms d) (orientedHeight w atoms d) :=
  match d with
  | .east => GridIsometry.refl _ _
  | .south => GridIsometry.clockwise _ _
  | .west => (GridIsometry.reflectX _ _).trans (GridIsometry.reflectY _ _)
  | .north => (GridIsometry.clockwise (height w) (width w atoms)).symm

def rotatedCoordinates (w : ℕ) (atoms : List Atom) (d : Direction)
    (p : Cell (width w atoms) (height w)) : ℕ × ℕ :=
  match d with
  | .east => (p.1.val,p.2.val)
  | .south => (height w-(p.2.val+1),p.1.val)
  | .west => (width w atoms-(p.1.val+1),height w-(p.2.val+1))
  | .north => (p.2.val,width w atoms-(p.1.val+1))

theorem rotation_coordinates (w : ℕ) (atoms : List Atom) (d : Direction)
    (p : Cell (width w atoms) (height w)) :
    (((rotation w atoms d).cells p).1.val,((rotation w atoms d).cells p).2.val) =
      rotatedCoordinates w atoms d p := by cases d <;> rfl

def anchor (w : ℕ) (atoms : List Atom) : Direction → ℕ × ℕ
  | .east | .south => (FiniteTools.radius w,FiniteTools.radius w)
  | .west => (FiniteTools.radius w+span w atoms+1,FiniteTools.radius w)
  | .north => (FiniteTools.radius w,FiniteTools.radius w+span w atoms+1)

def startCell (w : ℕ) (atoms : List Atom) : Cell (width w atoms) (height w) :=
  (⟨FiniteTools.radius w, by unfold width; omega⟩,
   ⟨FiniteTools.radius w, by unfold height FiniteTools.side; omega⟩)

def offsetX (w : ℕ) (atoms : List Atom) (d : Direction) (p : ℕ × ℕ) : ℕ :=
  padding w+p.1-(anchor w atoms d).1

def offsetY (w : ℕ) (atoms : List Atom) (d : Direction) (p : ℕ × ℕ) : ℕ :=
  padding w+p.2-(anchor w atoms d).2

theorem placement_fits (w : ℕ) (atoms : List Atom) (d : Direction) (p q : ℕ × ℕ)
    (htravel : Travels d p q (span w atoms))
    (hp : p.1 ≤ tileStride w ∧ p.2 ≤ tileStride w)
    (hq : q.1 ≤ tileStride w ∧ q.2 ≤ tileStride w) :
    offsetX w atoms d p+orientedWidth w atoms d ≤ tileSide w ∧
      offsetY w atoms d p+orientedHeight w atoms d ≤ tileSide w := by
  cases d <;>
    dsimp [Travels, offsetX, offsetY, anchor, orientedWidth, orientedHeight] at * <;>
    unfold width height FiniteTools.side FiniteTools.radius tileSide padding at * <;> omega

/-- The whole actual line rectangle, including every auxiliary box and thick wall, has a real grid placement. -/
def placement (w : ℕ) (atoms : List Atom) (d : Direction) (p q : ℕ × ℕ)
    (htravel : Travels d p q (span w atoms))
    (hp : p.1 ≤ tileStride w ∧ p.2 ≤ tileStride w)
    (hq : q.1 ≤ tileStride w ∧ q.2 ≤ tileStride w) :
    GridEmbedding (width w atoms) (height w) (tileSide w) (tileSide w) :=
  (rotation w atoms d).embedding.trans
    (GridEmbedding.translate (offsetX w atoms d p) (offsetY w atoms d p)
      (placement_fits w atoms d p q htravel hp hq).1 (placement_fits w atoms d p q htravel hp hq).2)

/-- World coordinates of an arbitrary scalar box position, including its one-cell phase shift. -/
def along (w : ℕ) (d : Direction) (p : ℕ × ℕ) (t : ℕ) : ℕ × ℕ :=
  match d with
  | .east => (padding w+p.1+t,padding w+p.2)
  | .south => (padding w+p.1,padding w+p.2+t)
  | .west => (padding w+p.1-t,padding w+p.2)
  | .north => (padding w+p.1,padding w+p.2-t)

theorem placement_cell (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (d : Direction) (p q : ℕ × ℕ)
    (htravel : Travels d p q (span w atoms))
    (hp : p.1 ≤ tileStride w ∧ p.2 ≤ tileStride w)
    (hq : q.1 ≤ tileStride w ∧ q.2 ≤ tileStride w) (phase : Bool) (l : Label w atoms) :
    (((placement w atoms d p q htravel hp hq).cells (cell w hw atoms phase l)).1.val,
      ((placement w atoms d p q htravel hp hq).cells (cell w hw atoms phase l)).2.val) =
      along w d p (position w atoms phase l) := by
  have hr := rotation_coordinates w atoms d (cell w hw atoms phase l)
  have hx := congrArg Prod.fst hr
  have hy := congrArg Prod.snd hr
  dsimp only at hx hy
  have hb := positions_bounds w hw phase atoms (position_mem w atoms phase l)
  have hphase := Bool.toNat_le phase
  apply Prod.ext
  all_goals dsimp [placement, GridEmbedding.trans, GridEmbedding.translate, GridIsometry.embedding]
  · rw [hx]
    cases d <;> dsimp [rotatedCoordinates, cell, along, Travels, offsetX, anchor] at * <;>
      unfold width height FiniteTools.side FiniteTools.radius padding at * <;> omega
  · rw [hy]
    cases d <;> dsimp [rotatedCoordinates, cell, along, Travels, offsetY, anchor] at * <;>
      unfold width height FiniteTools.side FiniteTools.radius padding at * <;> omega

end Line
end PushPuzzle.PushS.FiniteRouting
