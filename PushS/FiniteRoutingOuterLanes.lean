/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingStaticRows
public import PushS.FiniteRoutingOuterPorts

/-! Exact literal coordinates of both full exposed outer lanes of every actual line. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side

namespace Line

/-- A point at a fixed offset from the routed axis, indexed along the line. -/
@[expose] def outerAlong (w : ℕ) (d : Direction) (p : ℕ × ℕ) (north : Bool) (n : ℕ) : ℕ × ℕ :=
  match d with
  | .east => (padding w+p.1+n,if north then padding w+p.2-(w+1) else padding w+p.2+(w+1))
  | .south => (if north then padding w+p.1+(w+1) else padding w+p.1-(w+1),padding w+p.2+n)
  | .west => (padding w+p.1-n,if north then padding w+p.2+(w+1) else padding w+p.2-(w+1))
  | .north => (if north then padding w+p.1-(w+1) else padding w+p.1+(w+1),padding w+p.2-n)

theorem outerAlong_one (w : ℕ) (d : Direction) (p : ℕ × ℕ) (north : Bool) :
    outerAlong w d p north 1 = outerStart w d p north := by cases d <;> rfl

theorem outerAlong_finish (w : ℕ) (d : Direction) (p q : ℕ × ℕ) (length : ℕ)
    (ht : Travels d p q length) (north : Bool) : outerAlong w d p north length = outerAlong w d q north 0 := by
  cases d <;> cases north <;> dsimp [outerAlong,Travels] at ht ⊢ <;> apply Prod.ext <;> omega

theorem outerAlong_step (w : ℕ) (d : Direction) (p : ℕ × ℕ) (north : Bool) :
    Travels d (outerAlong w d p north 0) (outerAlong w d p north 1) 1 := by
  cases d <;> cases north <;> dsimp [outerAlong,Travels] <;> unfold padding <;> constructor <;> omega

theorem outerAlong_finish_add (w : ℕ) (d : Direction) (p q : ℕ × ℕ) (length : ℕ)
    (ht : Travels d p q length) (north : Bool) (n : ℕ) :
    outerAlong w d p north (length+n) = outerAlong w d q north n := by
  cases d <;> cases north <;> dsimp [outerAlong,Travels] at ht ⊢ <;> apply Prod.ext <;> omega

theorem outerAlong_boundary (w : ℕ) (face : Direction) (incoming north : Bool) :
    outerAlong w face (advance face.opposite (boundaryPoint w face) incoming.toNat) north incoming.toNat =
      outerAlong w face (boundaryPoint w face) north 0 := by
  cases face <;> cases incoming <;> cases north <;>
    dsimp [outerAlong,advance,boundaryPoint,Direction.opposite] <;> apply Prod.ext <;>
    unfold tileStride spacing padding <;> omega

end Line

namespace LineCode

/-- The rotated canonical outer-lane cell at the given line index. -/
@[expose] def laneSlot (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment) (north : Bool)
    (n : ℕ) (hn : n ≤ segmentLength c.segment+1) :
    Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height :=
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  (Line.rotation w atoms (segmentDirection c.segment)).cells
    (Line.outerCell w atoms north ⟨FiniteTools.radius w+n,by
      have hspan : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
      unfold Line.width FiniteTools.radius
      omega⟩)

/-- World coordinates of a rotated outer-lane cell. -/
@[expose] def laneWorld (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment) (north : Bool)
    (n : ℕ) (hn : n ≤ segmentLength c.segment+1) : ℕ × ℕ :=
  (PrimitiveCode.line c).world w hw (c.laneSlot w hw hc north n hn)

theorem laneWorld_eq (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment) (north : Bool)
    (n : ℕ) (hn : n ≤ segmentLength c.segment+1) :
    c.laneWorld w hw hc north n hn = Line.outerAlong w (segmentDirection c.segment) c.segment.start north n := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have hspan : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  let p : Cell (Line.width w atoms) (Line.height w) := Line.outerCell w atoms north
    ⟨FiniteTools.radius w+n,by unfold Line.width FiniteTools.radius; omega⟩
  have hr := Line.rotation_coordinates w atoms (segmentDirection c.segment) p
  have hx := congrArg Prod.fst hr
  have hy := congrArg Prod.snd hr
  dsimp only at hx hy
  have ht := segment_travels c.segment hc.1
  change (Line.offsetX w atoms (segmentDirection c.segment) c.segment.start+
      ((Line.rotation w atoms (segmentDirection c.segment)).cells p).1.val,
    Line.offsetY w atoms (segmentDirection c.segment) c.segment.start+
      ((Line.rotation w atoms (segmentDirection c.segment)).cells p).2.val) = _
  rw [hx,hy]
  clear hr hx hy
  cases hd : segmentDirection c.segment <;> cases north <;> simp only [hd] at ht ⊢ <;>
    dsimp [p,Line.outerCell,Line.laneY,Line.rotatedCoordinates,Line.outerAlong,Line.offsetX,Line.offsetY,Line.anchor,Travels] at * <;>
    apply Prod.ext <;> simp only [Line.width,Line.height,FiniteTools.side,FiniteTools.radius,padding] at * <;> omega

end LineCode
end PushPuzzle.PushS.FiniteRouting
