/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePathSites
public import PushS.FiniteSourceReadoutHops
public import PushS.FiniteRoutingRailReadout

/-! Actual source-table glyphs assemble into the complete physical path reader. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Line.width Line.height InventoryAssembly.board

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

namespace LineSite

/-- A canonical reader for this literal compiled line entry. -/
structure Readout (s : LineSite w hw v) (ha : (inventory w hw v).Admissible)
    (hc : ∀ l, SameComponent (inventory w hw v).board ((inventory w hw v).source l) ((inventory w hw v).target l)) where
  tracks : ComponentTracks ((s.orientation.inverse.axis (width w v) (height w v)).geometry.reorientInstance ((inventory w hw v).puzzle ha))
  glyph : Line.Readout.LineGlyph (((inventory w hw v).slotMatching ha hc).reorient
    (s.orientation.inverse.axis (width w v) (height w v)).geometry) tracks w s.atoms s.code.above
  embedding : ∀ p, glyph.embedding.cells p = s.canonicalEmbedding.cells p
  initial : glyph.initialPhase = s.code.initial

end LineSite

namespace TurnSite

/-- A canonical reader for this literal compiled turn entry. -/
structure Readout (s : TurnSite w hw v) (ha : (inventory w hw v).Admissible)
    (hc : ∀ l, SameComponent (inventory w hw v).board ((inventory w hw v).source l) ((inventory w hw v).target l)) where
  tracks : ComponentTracks ((s.orientation.inverse.axis (width w v) (height w v)).geometry.reorientInstance ((inventory w hw v).puzzle ha))
  glyph : Turn.Readout.TurnGlyph (((inventory w hw v).slotMatching ha hc).reorient
    (s.orientation.inverse.axis (width w v) (height w v)).geometry) tracks w
  embedding : ∀ p, glyph.embedding.cells p = s.canonicalEmbedding.cells p
  initial : glyph.initialPhase = s.code.initial

end TurnSite

namespace PathSite

variable {P : PathSpec} (s : PathSite w hw v P) (G : P.Geometry w)
    (ha : (inventory w hw v).Admissible)
    (hc : ∀ l, SameComponent (inventory w hw v).board ((inventory w hw v).source l) ((inventory w hw v).target l))

set_option maxHeartbeats 1000000 in
/-- The emitted sites supply all directions and literal slots of the indexed path. -/
def readout (L : ∀ i, (s.line i).Readout ha hc)
    (T : ∀ i hi, (s.turn G i hi).Readout ha hc) :
    PathGlyph ((inventory w hw v).slotMatching ha hc) w hw P where
  dx := tileStride w*s.location.1
  dy := tileStride w*s.location.2
  line i := (s.line i).hop ha hc (L i).glyph
  line_initial i := (L i).initial
  line_direction _ := rfl
  line_input_slot i phase := by
    rw [(s.line i).hop_inputSlot ha hc (L i).glyph phase (L i).embedding]
    change @coordinates (width w v) (height w v) ((s.line i).actualEmbedding.cells
      (Line.cell w hw (s.line i).atoms phase (Line.cutFirstLabel w (s.line i).atoms))) = _
    rw [(s.line i).actual_first_coordinates phase,s.line_location i]
    rfl
  line_output_slot i phase := by
    rw [(s.line i).hop_outputSlot ha hc (L i).glyph phase (L i).embedding]
    change @coordinates (width w v) (height w v) ((s.line i).actualEmbedding.cells
      (Line.cell w hw (s.line i).atoms phase (Line.cutLastLabel w (s.line i).atoms))) = _
    rw [(s.line i).actual_last_coordinates phase,s.line_location i]
    rfl
  turn i hi := (s.turn G i hi).hop ha hc (T i hi).glyph
  turn_initial i hi := (T i hi).initial
  turn_incoming _ _ := rfl
  turn_outgoing _ _ := rfl
  turn_input_slot i hi phase := by
    rw [(s.turn G i hi).hop_inputSlot ha hc (T i hi).glyph phase (T i hi).embedding]
    change @coordinates (width w v) (height w v) ((s.turn G i hi).actualEmbedding.cells
      (Turn.cell w phase 0)) = _
    rw [(s.turn G i hi).actual_slot_coordinates phase 0,s.turn_location G i hi]
    rfl
  turn_output_slot i hi phase := by
    rw [(s.turn G i hi).hop_outputSlot ha hc (T i hi).glyph phase (T i hi).embedding]
    change @coordinates (width w v) (height w v) ((s.turn G i hi).actualEmbedding.cells
      (Turn.cell w phase 1)) = _
    rw [(s.turn G i hi).actual_slot_coordinates phase 1,s.turn_location G i hi]
    rfl

end PathSite
end PushPuzzle.PushS.FiniteSourceInventory
