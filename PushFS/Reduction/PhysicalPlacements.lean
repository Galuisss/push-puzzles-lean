/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalInventory

/-! Literal complete-glyph placements on the actual physical source board. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory


open PhysicalBitmap

noncomputable def embedding (v : CellPlan.Source) (i : Index v) :
    GridEmbedding (PhysicalTiles.piece (tile i)).width (PhysicalTiles.piece (tile i)).height
      (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7) :=
  GridEmbedding.translate (PhysicalTiles.offset (position i) (tile i)).1 (PhysicalTiles.offset (position i) (tile i)).2
    (PhysicalTiles.fits v.1 i.val.1 (tile i)).1 (PhysicalTiles.fits v.1 i.val.1 (tile i)).2

theorem wall_membership (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (p : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)) :
    p∈(puzzle v hP hT).board.walls ↔∃i : Index v,
      ∃q : Cell (PhysicalTiles.piece (tile i)).width (PhysicalTiles.piece (tile i)).height,
        q∈(PhysicalTiles.piece (tile i)).board.walls ∧
          PhysicalTiles.coordinates (position i) (tile i) q=(p.1.val,p.2.val) := by
  change p∈(atlas v hP hT).walls ↔_
  rw [StorageAtlas.walls,Finset.mem_biUnion]
  constructor
  · rintro ⟨j,_,hj⟩
    obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hj
    exact ⟨(numbering v).symm j,q,hq,congrArg (fun p=>(p.1.val,p.2.val)) he⟩
  · rintro ⟨i,q,hq,he⟩
    obtain ⟨j,rfl⟩ := (numbering v).symm.surjective i
    refine ⟨j,Finset.mem_univ _,Finset.mem_map.mpr ⟨q,hq,?_⟩⟩
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he

theorem walls_agree (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) (i : Index v) :
    (embedding v i).WallsAgree (PhysicalTiles.piece (tile i)).board (atlas v hP hT).board := by
  intro p
  have hm := wall_membership v hP hT ((embedding v i).cells p)
  change (embedding v i).cells p∈(atlas v hP hT).walls ↔_ at hm
  change (embedding v i).cells p∈(atlas v hP hT).walls ↔_
  apply hm.trans
  constructor
  · rintro ⟨j,q,hq,he⟩
    change PhysicalTiles.coordinates (position j) (tile j) q=PhysicalTiles.coordinates (position i) (tile i) p at he
    exact (PhysicalTiles.walls_compatible v hP hT (key_eq i) (key_eq j) p q he.symm).mpr hq
  · intro hp
    exact ⟨i,p,hp,rfl⟩

end PushPuzzle.PushFS.Reduction.PhysicalInventory
