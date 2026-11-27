/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingReorientPlacement
public import PushS.FiniteRoutingPrimitiveGeometry

/-! Executable rectangular orientation witnesses for the actual routed line and F/G primitives. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS

namespace Line

def rectangleOrientation : Direction → RectOrientation
  | .east => ⟨false,false,false⟩
  | .south => ⟨true,true,false⟩
  | .west => ⟨false,true,true⟩
  | .north => ⟨true,false,true⟩

theorem rectangleOrientation_point (w : ℕ) (atoms : List Atom) (d : Direction) (p : Cell (width w atoms) (height w)) :
    coordinates ((rotation w atoms d).cells p) =
      (rectangleOrientation d).point (width w atoms) (height w) (coordinates p) := by
  cases d <;> rfl

private theorem rectangleOrientation_direction (d : Direction) :
    (rectangleOrientation d).direction .east = d := by
  cases d <;> rfl

theorem straighten_direction (d : Direction) : (rectangleOrientation d).inverse.direction d = .east := by
  have hh := RectOrientation.inverse_direction (rectangleOrientation d) .east
  rw [rectangleOrientation_direction] at hh
  exact hh

end Line

namespace Turn

def rectangleOrientation (incoming outgoing : Direction) : RectOrientation :=
  RectOrientation.choose incoming.opposite outgoing

private theorem rectangleOrientation_directions (d e : Direction) (h : Perpendicular d e) :
    (rectangleOrientation d e).direction .east = d ∧ (rectangleOrientation d e).direction .south = e := by
  cases d <;> cases e <;> simp [Perpendicular,rightTurn,Direction.opposite] at h <;> exact ⟨rfl,rfl⟩

theorem rectangleOrientation_point (w : ℕ) (d e : Direction) (h : Perpendicular d e)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) :
    coordinates ((orientation w d e).cells p) =
      (rectangleOrientation d e).point (FiniteTools.side w) (FiniteTools.side w) (coordinates p) := by
  have hx := p.1.isLt
  have hy := p.2.isLt
  cases d <;> cases e <;> simp [Perpendicular,rightTurn,Direction.opposite] at h
  all_goals apply Prod.ext <;> first | rfl | (change FiniteTools.side w-(FiniteTools.side w-(p.2.val+1)+1) = p.2.val; omega)

theorem straighten_directions (d e : Direction) (h : Perpendicular d e) :
    (rectangleOrientation d e).inverse.direction d = .east ∧
      (rectangleOrientation d e).inverse.direction e = .south := by
  have hd := rectangleOrientation_directions d e h
  have hi := RectOrientation.inverse_direction (rectangleOrientation d e) .east
  have ho := RectOrientation.inverse_direction (rectangleOrientation d e) .south
  rw [hd.1] at hi
  rw [hd.2] at ho
  exact ⟨hi,ho⟩

end Turn
end PushPuzzle.PushS.FiniteRouting
