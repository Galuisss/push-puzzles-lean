/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateTile

/-! Exact raw primitive wall, box and goal membership of the complete legal physical gate tile. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open scoped Classical

set_option maxRecDepth 131072
set_option maxHeartbeats 200000

private theorem box_marker {w h : ℕ} (B : Board w h) (s : State w h) (p : Cell w h) :
    (Encoding.tile B s p).box=true ↔p∈s.boxes := by
  simp only [Encoding.tile,decide_eq_true_eq]

private theorem full_tile (g : GateTileState) (p : C) :
    Encoding.tile (fullPuzzle g).board (fullPuzzle g).initial p=
      Bitmap.tile (Inventory.input g,p.1.val,p.2.val) := by
  have hm := Inventory.atlas_patch_membership g (Inventory.frontierContactProofs g)
  have he := Bitmap.tile_ext (fullAtlas g).input (Inventory.input g) rfl rfl hm (p.1.val,p.2.val)
  exact ((fullAtlas g).tile_eq p).symm.trans he

private theorem raw_flag (g : GateTileState) (p : C)
    (select : Encoding.Tile→Bool) (hzero : select Bitmap.emptyTile=false) :
    Bitmap.flag select (Inventory.input g,p.1.val,p.2.val)=true ↔
      ∃i : Inventory.Index g,∃q : Cell (Inventory.piece g i).width (Inventory.piece g i).height,
        select (Encoding.tile (Inventory.piece g i).board (Inventory.piece g i).initial q)=true ∧
        ((Inventory.offset g i).1+q.1.val,(Inventory.offset g i).2+q.2.val)=(p.1.val,p.2.val) := by
  simp only [Bitmap.flag,Inventory.input,Inventory.patches,List.any_eq_true,List.mem_map]
  constructor
  · rintro ⟨patch,⟨i,_,rfl⟩,hp⟩
    obtain ⟨q,he,hq⟩ := (Bitmap.instancePatch_truth (Inventory.piece g i)
      (Inventory.offset g i).1 (Inventory.offset g i).2
      (Inventory.fits g i).1 (Inventory.fits g i).2 p select hzero).mp hp
    exact ⟨i,q,hq,congrArg (fun p : C=>(p.1.val,p.2.val)) he⟩
  · rintro ⟨i,q,hq,he⟩
    refine ⟨Inventory.patch g i,⟨i,Inventory.mem_indices g i,rfl⟩,?_⟩
    apply (Bitmap.instancePatch_truth (Inventory.piece g i)
      (Inventory.offset g i).1 (Inventory.offset g i).2
      (Inventory.fits g i).1 (Inventory.fits g i).2 p select hzero).mpr
    refine ⟨q,?_,hq⟩
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he

theorem full_wall_membership (g : GateTileState) (p : C) :
    p∈(fullPuzzle g).board.walls ↔
      ∃ i : Inventory.Index g,∃ q : Cell (Inventory.piece g i).width (Inventory.piece g i).height,
        q∈(Inventory.piece g i).board.walls ∧
        ((Inventory.offset g i).1+q.1.val,(Inventory.offset g i).2+q.2.val)=(p.1.val,p.2.val) := by
  change p∈(fullAtlas g).walls ↔ _
  rw [StorageAtlas.walls,Finset.mem_biUnion]
  constructor
  · rintro ⟨j,_,hj⟩
    obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hj
    refine ⟨(Inventory.numbering g).symm j,q,hq,?_⟩
    exact congrArg (fun p : C=>(p.1.val,p.2.val)) he
  · rintro ⟨i,q,hq,he⟩
    obtain ⟨j,rfl⟩ := (Inventory.numbering g).symm.surjective i
    refine ⟨j,Finset.mem_univ j,Finset.mem_map.mpr ⟨q,hq,?_⟩⟩
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he

theorem full_box_membership (g : GateTileState) (p : C) :
    p∈(fullPuzzle g).initial.boxes ↔
      ∃ i : Inventory.Index g,∃ q : Cell (Inventory.piece g i).width (Inventory.piece g i).height,
        q∈(Inventory.piece g i).initial.boxes ∧
        ((Inventory.offset g i).1+q.1.val,(Inventory.offset g i).2+q.2.val)=(p.1.val,p.2.val) := by
  refine (box_marker (fullPuzzle g).board (fullPuzzle g).initial p).symm.trans ?_
  rw [full_tile]
  exact (raw_flag g p Encoding.Tile.box rfl).trans (by
    simp only [Encoding.tile,decide_eq_true_eq])

end PushPuzzle.PushFS.Reduction.GateTileRouting
