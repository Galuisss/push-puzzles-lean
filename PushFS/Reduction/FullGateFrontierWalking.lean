/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateLineFrames
public import PushFS.Reduction.AnnulusSeamWalkingGeometry
public import PushFS.Walking
public import PushFS.Reduction.FullGateBufferProfileWalking
public import PushFS.Reduction.FullGateLineWalking

/-! Literal fixed-inventory player connection from the buffered core to each actual first annular filler. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board profile profileOutside annularProfileBoxes annularBoxes

def firstLineIndex (g : GateTileState) (r : Fin 3) : Fin (curve (key g r)).length := ⟨0,frontier_first_valid _⟩

def firstLinePortal (g : GateTileState) (r : Fin 3) : Cell (lineInput g r (firstLineIndex g r)).width (lineInput g r (firstLineIndex g r)).height :=
  frontierLinePortal (fillerFlip (key g r) 0) (fillerSpan (key g r) 0) (filler_shape _ _ (frontier_first_valid _)).2.1
    (Inventory.initialPhase g r) (Inventory.targetPhase g r)

/-- The literal buffered-lead far corner is the actual first filler's outer-lane portal. -/
theorem frontier_seam_cell (g : GateTileState) (r : Fin 3) :
    (bufferLeadEmbedding g r).cells (Chain.corner 2301 1)=
      (lineEmbedding g r (firstLineIndex g r)).cells (firstLinePortal g r) := by
  have hh:=frontier_seam_corner (filler_shape (key g r) 0 (frontier_first_valid _)).2.1
    (fillerFlip (key g r) 0) (Inventory.initialPhase g r) (Inventory.targetPhase g r)
    (frontierOrientation g.core.isAND r) (frontierBufferOffset g r).1 (frontierBufferOffset g r).2
    (lineOffset (key g r) 0).1 (lineOffset (key g r) 0).2
    (frontier_shared_anchor g r (Inventory.initialPhase g r) (Inventory.targetPhase g r))
  have hb:=buffer_lead_coordinates g r (Chain.corner 2301 1)
  have hl:=line_coordinates g r (firstLineIndex g r) (firstLinePortal g r)
  change _=(lineOrientation (original (key g r) 0).travel (fillerFlip (key g r) 0)).coordinates _ _ _ _ _ at hl
  rw [frontier_first_orientation] at hl
  have he:=hb.trans (hh.trans hl.symm)
  exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

end PushPuzzle.PushFS.Reduction.GateTileRouting
