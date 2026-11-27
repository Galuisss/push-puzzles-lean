/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalProfileForeign

/-! Exact native-index placement of every actual mixed-profile glyph. -/
@[expose] public section
namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open PhysicalBitmap
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board
  StorageAtlas.profileOutside StorageAtlas.profileBoxes PhysicalTiles.marks

private theorem profile_split_index (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (i : Index v) :
    (atlas v hP hT).profileBoxes f=
      (PhysicalTiles.marks (f (numbering v i)) (tile i)).map (embedding v i).cells∪
        (atlas v hP hT).profileOutside f (numbering v i) := by
  obtain ⟨j,rfl⟩:=(numbering v).symm.surjective i
  simp only [Equiv.apply_symm_apply]
  have hm : (atlas v hP hT).pieceMarks f j=PhysicalTiles.marks (f j) (tile ((numbering v).symm j)):=by
    unfold PhysicalTiles.marks StorageAtlas.pieceMarks
    rfl
  have he : (atlas v hP hT).embedding j=embedding v ((numbering v).symm j):=rfl
  have hh:=(atlas v hP hT).profile_split f j
  rw [hm,he] at hh
  exact hh

theorem profile_place_index (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (i : Index v)
    (p : Cell (PhysicalTiles.piece (tile i)).width (PhysicalTiles.piece (tile i)).height) :
    (embedding v i).extend ((atlas v hP hT).profileOutside f (numbering v i))
      ⟨p,PhysicalTiles.marks (f (numbering v i)) (tile i)⟩=
      (atlas v hP hT).profileAt f ((embedding v i).cells p) := by
  apply State.ext
  · rfl
  · exact (profile_split_index v hP hT f i).symm

end PushPuzzle.PushFS.Reduction.PhysicalInventory
