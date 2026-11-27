/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLinePorts
public import PushS.FiniteRoutingWorldCoordinates
public import PushS.FiniteRoutingMacroContacts
public import PushS.FiniteGeometrySimp

/-! Exact integer coordinates around the shared physical origin of a source port. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls Line.program Line.span FiniteTools.side

/-- Integer coordinates centered at the shared source port, with its outward direction first. -/
@[expose] def portCoordinates (w : ℕ) (pos : ℕ × ℕ) (face : Direction) (a : ℕ × ℕ) : ℤ × ℤ :=
  let b := macroShift w pos (Line.along w face (boundaryPoint w face) 0)
  match face with
  | .east => (a.1-b.1,a.2-b.2)
  | .south => (a.2-b.2,b.1-a.1)
  | .west => (b.1-a.1,b.2-a.2)
  | .north => (b.2-a.2,a.1-b.1)

attribute [local finite_line_coords] portCoordinates macroShift Line.along boundaryPoint
  Line.rotatedCoordinates Line.offsetX Line.offsetY Line.anchor Direction.opposite

namespace LineCode

private theorem portCoordinates_action (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (pos : ℕ × ℕ) (face : Direction) (reverse : Bool)
    (hd : segmentDirection c.segment = if reverse then face.opposite else face) (p : c.ActionCell w) :
    let base := portCoordinates w pos face (macroShift w pos (Line.along w (segmentDirection c.segment) c.segment.start 0))
    portCoordinates w pos face (macroShift w pos (c.actionWorld w hw p)) =
      if reverse then
        (base.1+FiniteTools.radius w-p.1.val,base.2+FiniteTools.radius w-p.2.val)
      else (base.1+p.1.val-FiniteTools.radius w,base.2+p.2.val-FiniteTools.radius w) := by
  have hs := Line.program_span_of_bound w _ (c.above != c.desiredSide) hc.2.1
  have ht := segment_travels c.segment hc.1
  have hpx := p.1.isLt
  have hpy := p.2.isLt
  rw [LineCode.actionWorld_eq,hd]
  rw [hd] at ht
  cases reverse <;> cases face <;>
    simp only [Bool.false_eq_true,ite_false,ite_true] at * <;>
    simp only [finite_line_coords] at * <;> dsimp [Travels] at * <;>
    apply Prod.ext <;> simp only [Nat.cast_add,Line.width,Line.height,FiniteTools.side,
      FiniteTools.radius,hs,padding,tileStride,spacing] at * <;> omega

private theorem portCoordinates_base (w : ℕ) (pos : ℕ × ℕ) (face : Direction) :
    portCoordinates w pos face (macroShift w pos (Line.along w face (boundaryPoint w face) 0)) = (0,0) := by
  cases face <;> simp [portCoordinates]

theorem portCoordinates_end (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (pos : ℕ × ℕ) (face : Direction) (incoming : Bool)
    (hd : segmentDirection c.segment = face)
    (he : c.segment.finish = advance face.opposite (boundaryPoint w face) incoming.toNat)
    (p : c.ActionCell w) :
    portCoordinates w pos face (macroShift w pos (c.actionWorld w hw p)) =
      ((p.1.val : ℤ)-FiniteTools.radius w-segmentLength c.segment-incoming.toNat,
        (p.2.val : ℤ)-FiniteTools.radius w) := by
  rw [portCoordinates_action w hw c hc pos face false hd p]
  have ht := segment_travels c.segment hc.1
  rw [hd,he] at ht
  have hi := Bool.toNat_le incoming
  have hbase : portCoordinates w pos face (macroShift w pos (Line.along w (segmentDirection c.segment) c.segment.start 0)) =
      (-((segmentLength c.segment : ℤ)+incoming.toNat),0) := by
    rw [hd]
    cases face <;> simp only [finite_line_coords] at * <;> dsimp [Travels,advance] at * <;>
      apply Prod.ext <;> simp only [padding,tileStride,spacing] at * <;> omega
  simp only [hbase,Bool.false_eq_true,ite_false]
  apply Prod.ext <;> dsimp only <;> omega

theorem portCoordinates_start (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (pos : ℕ × ℕ) (face : Direction)
    (hd : segmentDirection c.segment = face.opposite) (he : c.segment.start = boundaryPoint w face)
    (p : c.ActionCell w) :
    portCoordinates w pos face (macroShift w pos (c.actionWorld w hw p)) =
      ((FiniteTools.radius w : ℤ)-p.1.val,(FiniteTools.radius w : ℤ)-p.2.val) := by
  rw [portCoordinates_action w hw c hc pos face true hd p]
  have hbase : portCoordinates w pos face (macroShift w pos (Line.along w (segmentDirection c.segment) c.segment.start 0)) = (0,0) := by
    rw [hd,he]
    have heq : Line.along w face.opposite (boundaryPoint w face) 0 = Line.along w face (boundaryPoint w face) 0 := by
      cases face <;> rfl
    rw [heq]
    exact portCoordinates_base w pos face
  simp only [hbase,ite_true,zero_add]

end LineCode

theorem portCoordinates_neighbor (w : ℕ) (pos other a : ℕ × ℕ) (face : Direction)
    (hn : neighbor face pos = some other) :
    (portCoordinates w pos face a).1+(portCoordinates w other face.opposite a).1 = 0 ∧
      (portCoordinates w pos face a).2+(portCoordinates w other face.opposite a).2 = 0 := by
  have ht := neighbor_travels hn
  cases face <;> dsimp [Travels] at ht
  all_goals dsimp [portCoordinates,macroShift,Line.along,boundaryPoint,Direction.opposite]
  all_goals rw [ht.1,ht.2]
  all_goals simp only [Nat.cast_add,mul_add]; constructor <;> ring

end PushPuzzle.PushS.FiniteRouting
