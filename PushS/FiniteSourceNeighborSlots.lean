/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePathSlots
public import PushS.FiniteRoutingNeighborSlots

/-! The actual source-table placements of each turn's fixed neighboring stock. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Line.width Line.height

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

namespace LineSite

theorem actual_second_coordinates (s : LineSite w hw v) (phase : Bool) :
    coordinates (s.actualEmbedding.cells (Line.cell w hw s.atoms phase
      (Line.secondLabel w (segmentLength s.code.segment) (s.code.above != s.code.desiredSide)))) =
      shiftPoint (tileStride w*((codes w v).get s.index).1.1) (tileStride w*((codes w v).get s.index).1.2)
        (s.code.secondWorld w hw phase) := by
  change coordinates ((primitiveEmbedding w hw v s.index (.line s.code) s.code_eq).cells (s.code.secondSlot w hw phase)) = _
  rw [primitiveEmbedding_coordinates]
  change shiftPoint s.dx s.dy (coordinates (s.code.secondSlot w hw phase)) = _
  rw [s.dx_eq,s.dy_eq]
  simp only [LineCode.secondWorld,PrimitiveCode.world,shiftPoint,coordinates,Nat.add_assoc]

private theorem actual_penultimate_coordinates (s : LineSite w hw v) (phase : Bool) :
    coordinates (s.actualEmbedding.cells (Line.cell w hw s.atoms phase
      (Line.penultimateLabel w (segmentLength s.code.segment) (s.code.above != s.code.desiredSide)))) =
      shiftPoint (tileStride w*((codes w v).get s.index).1.1) (tileStride w*((codes w v).get s.index).1.2)
        (s.code.penultimateWorld w hw phase) := by
  change coordinates ((primitiveEmbedding w hw v s.index (.line s.code) s.code_eq).cells (s.code.penultimateSlot w hw phase)) = _
  rw [primitiveEmbedding_coordinates]
  change shiftPoint s.dx s.dy (coordinates (s.code.penultimateSlot w hw phase)) = _
  rw [s.dx_eq,s.dy_eq]
  simp only [LineCode.penultimateWorld,PrimitiveCode.world,shiftPoint,coordinates,Nat.add_assoc]

end LineSite

namespace TurnSite

private theorem actual_fixture_coordinates (s : TurnSite w hw v) (successor : Bool) :
    coordinates (s.actualEmbedding.cells
      (FiniteTools.turnMixedCell w false false (if successor then .successor else .predecessor))) =
      shiftPoint (tileStride w*((codes w v).get s.index).1.1) (tileStride w*((codes w v).get s.index).1.2)
        (s.code.fixtureWorld w hw successor) := by
  change coordinates ((primitiveEmbedding w hw v s.index (.turn s.code) s.code_eq).cells (s.code.fixtureSlot w successor)) = _
  rw [primitiveEmbedding_coordinates w hw v s.index (.turn s.code) s.code_eq (s.code.fixtureSlot w successor)]
  change shiftPoint s.dx s.dy (coordinates (s.code.fixtureSlot w successor)) = _
  have hx : s.dx = tileStride w*((codes w v).get s.index).1.1+PrimitiveCode.offsetX w (.turn s.code) := by
    change tileStride w*((codes w v).get s.index).1.1+PrimitiveCode.offsetX w ((codes w v).get s.index).2 = _
    rw [s.code_eq]
  have hy : s.dy = tileStride w*((codes w v).get s.index).1.2+PrimitiveCode.offsetY w (.turn s.code) := by
    change tileStride w*((codes w v).get s.index).1.2+PrimitiveCode.offsetY w ((codes w v).get s.index).2 = _
    rw [s.code_eq]
  rw [hx,hy]
  simp only [TurnCode.fixtureWorld,PrimitiveCode.world,shiftPoint,coordinates,Nat.add_assoc]

end TurnSite

namespace PathSite

variable {P : PathSpec} (s : PathSite w hw v P) (G : P.Geometry w)

private theorem cell_ext {W H : ℕ} {p q : Cell W H} (h : coordinates p = coordinates q) : p = q :=
  Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))

theorem predecessor_cells (i : Fin P.segments.length) (hi : P.hasTurn i.val) :
    (s.line i).actualEmbedding.cells (Line.cell w hw (s.line i).atoms false
      (Line.penultimateLabel w (segmentLength (s.line i).code.segment) ((s.line i).code.above != (s.line i).code.desiredSide))) =
      (s.turn G i hi).actualEmbedding.cells (FiniteTools.turnMixedCell w false false .predecessor) := by
  apply cell_ext
  have hl := (s.line i).actual_penultimate_coordinates false
  have hr := (s.turn G i hi).actual_fixture_coordinates false
  simp only [Bool.false_eq_true,ite_false] at hr
  rw [s.line_location i] at hl
  rw [s.turn_location G i hi] at hr
  exact hl.trans ((congrArg (shiftPoint (tileStride w*s.location.1) (tileStride w*s.location.2))
    ((P.junction_contract w G i.val hi).incoming_penultimate_predecessor w hw _ _ _)).trans hr.symm)

theorem successor_cells (i : Fin P.segments.length) (hi : P.hasTurn i.val) :
    (s.line ⟨i.val+1,hi.1⟩).actualEmbedding.cells (Line.cell w hw (s.line ⟨i.val+1,hi.1⟩).atoms true
      (Line.secondLabel w (segmentLength (s.line ⟨i.val+1,hi.1⟩).code.segment)
        ((s.line ⟨i.val+1,hi.1⟩).code.above != (s.line ⟨i.val+1,hi.1⟩).code.desiredSide))) =
      (s.turn G i hi).actualEmbedding.cells (FiniteTools.turnMixedCell w false false .successor) := by
  apply cell_ext
  have hl := (s.line ⟨i.val+1,hi.1⟩).actual_second_coordinates true
  have hr := (s.turn G i hi).actual_fixture_coordinates true
  simp only [ite_true] at hr
  rw [s.line_location ⟨i.val+1,hi.1⟩] at hl
  rw [s.turn_location G i hi] at hr
  exact hl.trans ((congrArg (shiftPoint (tileStride w*s.location.1) (tileStride w*s.location.2))
    ((P.junction_contract w G i.val hi).outgoing_second_successor w hw _ _ _)).trans hr.symm)

end PathSite
end PushPuzzle.PushS.FiniteSourceInventory
