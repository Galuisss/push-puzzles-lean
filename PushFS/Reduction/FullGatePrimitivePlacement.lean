/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateInventory

/-! Literal primitive placements on the actual complete gate, indexed by their physical inventory identities. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


set_option maxRecDepth 65536

def primitiveEmbedding (g : GateTileState) (i : Inventory.Index g) :
    GridEmbedding (Inventory.piece g i).width (Inventory.piece g i).height 200007 198068 :=
  GridEmbedding.translate (Inventory.offset g i).1 (Inventory.offset g i).2 (Inventory.fits g i).1 (Inventory.fits g i).2

/-- Each complete real primitive sees exactly its own actual walls inside the full physical gate board. -/
theorem primitive_walls_agree (g : GateTileState) (i : Inventory.Index g) :
    (primitiveEmbedding g i).WallsAgree (Inventory.piece g i).board (fullAtlas g).board := by
  intro p
  have hm := full_wall_membership g ((primitiveEmbedding g i).cells p)
  change (primitiveEmbedding g i).cells p∈(fullAtlas g).walls ↔_ at hm
  change (primitiveEmbedding g i).cells p∈(fullAtlas g).walls ↔_
  apply hm.trans
  constructor
  · rintro ⟨j,q,hq,he⟩
    change ((Inventory.offset g j).1+q.1.val,(Inventory.offset g j).2+q.2.val)=
      ((Inventory.offset g i).1+p.1.val,(Inventory.offset g i).2+p.2.val) at he
    exact ((Inventory.contactProofs g (Inventory.frontierContactProofs g)).walls_compatible i j p q he.symm).mpr hq
  · intro hp
    exact ⟨i,p,hp,rfl⟩

end PushPuzzle.PushFS.Reduction.GateTileRouting
