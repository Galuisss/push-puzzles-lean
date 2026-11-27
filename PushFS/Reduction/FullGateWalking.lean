/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGatePrimitivePlacement
public import PushFS.Reduction.GateLeadWalking
public import PushFS.Gadgets.Wires.Chain.CoveredPlacement

/-! Literal core-corner walks in the complete gate with every real annular box held fixed. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def coreEmbedding (g : GateTileState) : GridEmbedding 81 107 200007 198068 :=
  primitiveEmbedding g (.inl 0)

attribute [local irreducible] StorageAtlas.initial StorageAtlas.board

end PushPuzzle.PushFS.Reduction.GateTileRouting
