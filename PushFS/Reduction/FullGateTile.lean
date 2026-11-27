/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusAtlas
public import PushFS.Reduction.AnnulusFrontier

/-! The unconditional complete physical finite gate catalog, with its exact dense machine bitmap and C1 matching. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Turing.MultiTapeTM ComputableInPolyTime

/-- All actual core, buffered leads, annular lines, protected turns and output guards in one physical atlas. -/
noncomputable def fullAtlas (g : GateTileState) := Inventory.atlas g (Inventory.frontierContactProofs g)

/-- The full legal unlabelled physical gate tile, retaining every auxiliary box and target. -/
noncomputable def fullPuzzle (g : GateTileState) : Instance := Inventory.puzzle g (Inventory.frontierContactProofs g)

noncomputable def fullSlotMatching (g : GateTileState) :
    SlotMatching (fullPuzzle g) ((i : Fin (Fintype.card (Inventory.Index g)))×Inventory.AtlasLabels g i) :=
  Inventory.slotMatching g (Inventory.frontierContactProofs g)

/-- Exact equality with the complete actual emitted physical bitmap. -/
theorem full_data (g : GateTileState) : Encoding.data (fullPuzzle g)=Inventory.data g :=
  Inventory.puzzle_data g (Inventory.frontierContactProofs g)

/-- Every actual primitive stencil agrees with the whole physical gate board at all its cells. -/
theorem full_walls_agree (g : GateTileState) (i : Fin (Fintype.card (Inventory.Index g))) :
    ((fullAtlas g).embedding i).WallsAgree ((fullAtlas g).piece i).board (fullPuzzle g).board :=
  (fullAtlas g).walls_agree i

end PushPuzzle.PushFS.Reduction.GateTileRouting
