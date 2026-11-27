/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateBufferedWalking
public import PushFS.Gadgets.Wires.Catalog.EndpointBounds

/-! Real buffered-lead corner transit with the complete annular source inventory present. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board annularBoxes

theorem buffer_lead_coordinates (g : GateTileState) (r : Fin 3) (p : Chain.C 2301) :
    (((bufferLeadEmbedding g r).cells p).1.val,((bufferLeadEmbedding g r).cells p).2.val)=
      (frontierOrientation g.core.isAND r).coordinates 2306 21
        (frontierBufferOffset g r).1 (frontierBufferOffset g r).2 p := by
  have hh:=frontier_lead_coordinates g.core.isAND 2301 r p
  have hx:=congrArg Prod.fst hh
  have hy:=congrArg Prod.snd hh
  apply Prod.ext
  · change (bufferOffset g.core.isAND).1+((frontierLeadPlacement g.core.isAND 2301 r).cells p).1.val=
      (bufferOffset g.core.isAND).1+GateLead.dx g.core.isAND 2301 (frontierBufferIndex r)+
        (((frontierOrientation g.core.isAND r).axis 2306 21).geometry.cells p).1.val
    change GateLead.dx g.core.isAND 2301 (frontierBufferIndex r)+
      (((frontierOrientation g.core.isAND r).axis 2306 21).geometry.cells p).1.val=
      ((frontierLeadPlacement g.core.isAND 2301 r).cells p).1.val at hx
    omega
  · change (bufferOffset g.core.isAND).2+((frontierLeadPlacement g.core.isAND 2301 r).cells p).2.val=
      (bufferOffset g.core.isAND).2+GateLead.dy g.core.isAND 2301 (frontierBufferIndex r)+
        (((frontierOrientation g.core.isAND r).axis 2306 21).geometry.cells p).2.val
    change GateLead.dy g.core.isAND 2301 (frontierBufferIndex r)+
      (((frontierOrientation g.core.isAND r).axis 2306 21).geometry.cells p).2.val=
      ((frontierLeadPlacement g.core.isAND 2301 r).cells p).2.val at hy
    omega

end PushPuzzle.PushFS.Reduction.GateTileRouting
