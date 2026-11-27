/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceMeshPorts
public import PushS.FiniteRoutingOuterLanes

/-! Producer outer-lane endpoints are the literal two free shoulders of their coarse-grid port. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Line.width Line.height

/-- The coarse-grid vertex indexing the chosen face. -/
@[expose] def meshFaceBase (face : Direction) (pos : ℕ × ℕ) : ℕ × ℕ :=
  match face with
  | .east => (pos.1+1,pos.2)
  | .south => (pos.1,pos.2+1)
  | .west | .north => pos

/-- The boundary point one walking lane away from the port axis. -/
@[expose] def shoulder (w : ℕ) (face : Direction) (north : Bool) : ℕ × ℕ :=
  Line.outerAlong w face (boundaryPoint w face) north 0

/-- The canonical lane corresponding to the lower coordinate shoulder. -/
@[expose] def lowNorth : Direction → Bool
  | .east | .north => true
  | .west | .south => false

/-- The transverse coordinate of a port shoulder along its mesh edge. -/
@[expose] def shoulderOffset (w : ℕ) (face : Direction) (north : Bool) : ℕ :=
  if north = lowNorth face then 25*spacing w-(w+1) else 25*spacing w+(w+1)

theorem shoulderOffset_low (w : ℕ) (face : Direction) :
    shoulderOffset w face (lowNorth face) = 25*spacing w-(w+1) := by simp [shoulderOffset]

theorem shoulderOffset_high (w : ℕ) (face : Direction) :
    shoulderOffset w face (!(lowNorth face)) = 25*spacing w+(w+1) := by
  cases face <;> simp [shoulderOffset,lowNorth]

theorem shoulderOffset_free (w : ℕ) (face : Direction) (north : Bool) :
    shoulderOffset w face north ≤ tileStride w ∧
      (shoulderOffset w face north+w < 25*spacing w ∨ 25*spacing w+w < shoulderOffset w face north) := by
  unfold shoulderOffset
  split_ifs <;> unfold tileStride spacing <;> omega

theorem macro_shoulder (w : ℕ) (face : Direction) (pos : ℕ × ℕ) (north : Bool) :
    macroShift w pos (shoulder w face north) =
      if face = .east ∨ face = .west then
        (tileStride w*(meshFaceBase face pos).1+padding w,
          tileStride w*(meshFaceBase face pos).2+padding w+shoulderOffset w face north)
      else
        (tileStride w*(meshFaceBase face pos).1+padding w+shoulderOffset w face north,
          tileStride w*(meshFaceBase face pos).2+padding w) := by
  cases face <;> cases north <;> dsimp [macroShift,shoulder,meshFaceBase,Line.outerAlong,boundaryPoint,shoulderOffset,lowNorth] <;>
    apply Prod.ext <;> simp only [Nat.mul_add,Nat.mul_one,tileStride,spacing,padding] <;> omega

namespace LineSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

/-- The last interior cell of the chosen canonical outer lane. -/
@[expose] def endLane (north : Bool) : Cell (Line.width w s.atoms) (Line.height w) :=
  Line.outerCell w s.atoms north ⟨FiniteTools.radius w+Line.span w s.atoms,by unfold Line.width; omega⟩

theorem actual_endLane_coordinates (north : Bool) :
    coordinates (s.actualEmbedding.cells (s.endLane north)) = macroShift w ((codes w v).get s.index).1
      (Line.outerAlong w (segmentDirection s.code.segment) s.code.segment.finish north 0) := by
  have hspan : Line.span w s.atoms = segmentLength s.code.segment := Line.program_span_of_bound w _ _ s.good.2.1
  have he : (Line.rotation w s.atoms (segmentDirection s.code.segment)).cells (s.endLane north) =
      s.code.laneSlot w hw s.good north (segmentLength s.code.segment) (by omega) := by
    congr 1
    apply Prod.ext
    · apply Fin.ext
      change FiniteTools.radius w+Line.span w s.atoms = FiniteTools.radius w+segmentLength s.code.segment
      rw [hspan]
    · rfl
  rw [s.actual_cell_coordinates,he]
  change macroShift w ((codes w v).get s.index).1 (s.code.laneWorld w hw s.good north _ _) = _
  rw [LineCode.laneWorld_eq,Line.outerAlong_finish w _ s.code.segment.start s.code.segment.finish _
    (segment_travels _ s.good.1)]

theorem producer_endLane_coordinates (face : Direction) (hd : segmentDirection s.code.segment = face)
    (he : s.code.segment.finish = boundaryPoint w face) (north : Bool) :
    coordinates (s.actualEmbedding.cells (s.endLane north)) =
      macroShift w ((codes w v).get s.index).1 (shoulder w face north) := by
  rw [s.actual_endLane_coordinates,hd,he]
  rfl

end LineSite
end PushPuzzle.PushS.FiniteSourceInventory
