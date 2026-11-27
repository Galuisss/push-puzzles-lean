/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceTurnGlyph

/-! Concrete compiled table sites form direction-aligned relay hops with exact normal interface cells. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

attribute [local irreducible] width height codes Line.width Line.height Line.walls InventoryAssembly.walls InventoryAssembly.board

namespace LineSite

variable (s : LineSite w hw v)
    (ha : (inventory w hw v).Admissible)
    (hc : ∀ l, SameComponent (inventory w hw v).board ((inventory w hw v).source l) ((inventory w hw v).target l))
    {A : ComponentTracks ((s.orientation.inverse.axis (width w v) (height w v)).geometry.reorientInstance ((inventory w hw v).puzzle ha))}
    (g : Line.Readout.LineGlyph (((inventory w hw v).slotMatching ha hc).reorient
      (s.orientation.inverse.axis (width w v) (height w v)).geometry) A w s.atoms s.code.above)

set_option maxHeartbeats 1000000 in
def hop : LineHop ((inventory w hw v).slotMatching ha hc) where
  orientation := s.orientation.inverse
  direction := segmentDirection s.code.segment
  aligned := Line.straighten_direction _
  tracks := A
  w := w
  length := segmentLength s.code.segment
  switch := s.code.above != s.code.desiredSide
  above := s.code.above
  glyph := g

theorem hop_inputSlot (phase : Bool)
    (he : ∀ p, g.embedding.cells p = s.canonicalEmbedding.cells p) :
    (s.hop ha hc g).inputSlot phase = s.actualEmbedding.cells (Line.cell w hw s.atoms phase (Line.cutFirstLabel w s.atoms)) := by
  change (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells.symm
    (g.embedding.cells (Line.cell w hw s.atoms phase (Line.cutFirstLabel w s.atoms))) = _
  rw [he,←s.placed_normal]
  exact (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells.symm_apply_apply _

theorem hop_outputSlot (phase : Bool)
    (he : ∀ p, g.embedding.cells p = s.canonicalEmbedding.cells p) :
    (s.hop ha hc g).outputSlot phase = s.actualEmbedding.cells (Line.cell w hw s.atoms phase (Line.cutLastLabel w s.atoms)) := by
  change (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells.symm
    (g.embedding.cells (Line.cell w hw s.atoms phase (Line.cutLastLabel w s.atoms))) = _
  rw [he,←s.placed_normal]
  exact (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells.symm_apply_apply _

omit ha hc g in
theorem actual_first_coordinates (phase : Bool) :
    coordinates (s.actualEmbedding.cells (Line.cell w hw s.atoms phase (Line.cutFirstLabel w s.atoms))) =
      shiftPoint (tileStride w*((codes w v).get s.index).1.1) (tileStride w*((codes w v).get s.index).1.2)
        (s.code.firstWorld w hw phase) := by
  change coordinates ((primitiveEmbedding w hw v s.index (.line s.code) s.code_eq).cells (s.code.firstSlot w hw phase)) = _
  rw [primitiveEmbedding_coordinates]
  change shiftPoint s.dx s.dy (coordinates (s.code.firstSlot w hw phase)) = _
  rw [s.dx_eq,s.dy_eq]
  simp only [LineCode.firstWorld,PrimitiveCode.world,shiftPoint,coordinates,Nat.add_assoc]

omit ha hc g in
theorem actual_last_coordinates (phase : Bool) :
    coordinates (s.actualEmbedding.cells (Line.cell w hw s.atoms phase (Line.cutLastLabel w s.atoms))) =
      shiftPoint (tileStride w*((codes w v).get s.index).1.1) (tileStride w*((codes w v).get s.index).1.2)
        (s.code.lastWorld w hw phase) := by
  change coordinates ((primitiveEmbedding w hw v s.index (.line s.code) s.code_eq).cells (s.code.lastSlot w hw phase)) = _
  rw [primitiveEmbedding_coordinates]
  change shiftPoint s.dx s.dy (coordinates (s.code.lastSlot w hw phase)) = _
  rw [s.dx_eq,s.dy_eq]
  simp only [LineCode.lastWorld,PrimitiveCode.world,shiftPoint,coordinates,Nat.add_assoc]

end LineSite

namespace TurnSite

variable (s : TurnSite w hw v)
    (ha : (inventory w hw v).Admissible)
    (hc : ∀ l, SameComponent (inventory w hw v).board ((inventory w hw v).source l) ((inventory w hw v).target l))
    {A : ComponentTracks ((s.orientation.inverse.axis (width w v) (height w v)).geometry.reorientInstance ((inventory w hw v).puzzle ha))}
    (g : Turn.Readout.TurnGlyph (((inventory w hw v).slotMatching ha hc).reorient
      (s.orientation.inverse.axis (width w v) (height w v)).geometry) A w)

set_option maxHeartbeats 1000000 in
def hop : TurnHop ((inventory w hw v).slotMatching ha hc) where
  orientation := s.orientation.inverse
  incoming := s.code.incoming
  outgoing := s.code.outgoing
  incoming_aligned := (Turn.straighten_directions _ _ s.perpendicular).1
  outgoing_aligned := (Turn.straighten_directions _ _ s.perpendicular).2
  tracks := A
  w := w
  glyph := g

theorem hop_inputSlot (phase : Bool)
    (he : ∀ p, g.embedding.cells p = s.canonicalEmbedding.cells p) :
    (s.hop ha hc g).inputSlot phase = s.actualEmbedding.cells (Turn.cell w phase 0) := by
  change (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells.symm
    (g.embedding.cells (Turn.cell w phase 0)) = _
  rw [he,←s.placed_normal]
  exact (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells.symm_apply_apply _

theorem hop_outputSlot (phase : Bool)
    (he : ∀ p, g.embedding.cells p = s.canonicalEmbedding.cells p) :
    (s.hop ha hc g).outputSlot phase = s.actualEmbedding.cells (Turn.cell w phase 1) := by
  change (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells.symm
    (g.embedding.cells (Turn.cell w phase 1)) = _
  rw [he,←s.placed_normal]
  exact (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells.symm_apply_apply _

omit ha hc g in
theorem actual_slot_coordinates (phase : Bool) (l : Fin 2) :
    coordinates (s.actualEmbedding.cells (Turn.cell w phase l)) =
      shiftPoint (tileStride w*((codes w v).get s.index).1.1) (tileStride w*((codes w v).get s.index).1.2)
        (s.code.worldSlot w hw phase l) := by
  change coordinates ((primitiveEmbedding w hw v s.index (.turn s.code) s.code_eq).cells (s.code.slot w phase l)) = _
  rw [primitiveEmbedding_coordinates w hw v s.index (.turn s.code) s.code_eq (s.code.slot w phase l)]
  change shiftPoint s.dx s.dy (coordinates (s.code.slot w phase l)) = _
  have hx : s.dx = tileStride w*((codes w v).get s.index).1.1+PrimitiveCode.offsetX w (.turn s.code) := by
    change tileStride w*((codes w v).get s.index).1.1+PrimitiveCode.offsetX w ((codes w v).get s.index).2 = _
    rw [s.code_eq]
  have hy : s.dy = tileStride w*((codes w v).get s.index).1.2+PrimitiveCode.offsetY w (.turn s.code) := by
    change tileStride w*((codes w v).get s.index).1.2+PrimitiveCode.offsetY w ((codes w v).get s.index).2 = _
    rw [s.code_eq]
  rw [hx,hy]
  simp only [TurnCode.worldSlot,PrimitiveCode.world,shiftPoint,coordinates,Nat.add_assoc]

end TurnSite
end PushPuzzle.PushS.FiniteSourceInventory
