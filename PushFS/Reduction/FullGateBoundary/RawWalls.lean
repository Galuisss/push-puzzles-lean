/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateTile

/-! True primitive wall ownership of the complete legal gate board. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary


theorem raw_wall_membership (g : GateTileState) (p : C) :
    p∈(fullPuzzle g).board.walls ↔
      ∃i : Inventory.Index g,∃q : Cell (Inventory.piece g i).width (Inventory.piece g i).height,
        q∈(Inventory.piece g i).board.walls ∧
        ((Inventory.offset g i).1+q.1.val,(Inventory.offset g i).2+q.2.val)=(p.1.val,p.2.val) := by
  change p∈(fullAtlas g).walls ↔_
  rw [StorageAtlas.walls,Finset.mem_biUnion]
  constructor
  · rintro ⟨j,_,hj⟩
    obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hj
    exact ⟨(Inventory.numbering g).symm j,q,hq,congrArg (fun p : C=>(p.1.val,p.2.val)) he⟩
  · rintro ⟨i,q,hq,he⟩
    obtain ⟨j,rfl⟩:=(Inventory.numbering g).symm.surjective i
    refine ⟨j,Finset.mem_univ j,Finset.mem_map.mpr ⟨q,hq,?_⟩⟩
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary
