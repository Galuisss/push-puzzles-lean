/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.Bitmap

/-! Complete bitmap rendering depends only on actual patch membership and the one global rectangle/player. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.Bitmap


private theorem flag_ext (x y : Input) (hm : ∀ p,p∈x.patches ↔ p∈y.patches)
    (select : Encoding.Tile→Bool) (p : ℕ×ℕ) : flag select (x,p)=flag select (y,p) := by
  apply Bool.eq_iff_iff.mpr
  simp only [flag,List.any_eq_true]
  constructor
  · rintro ⟨patch,hp,hflag⟩
    exact ⟨patch,(hm patch).mp hp,hflag⟩
  · rintro ⟨patch,hp,hflag⟩
    exact ⟨patch,(hm patch).mpr hp,hflag⟩

theorem tile_ext (x y : Input) (hpx : x.playerX=y.playerX) (hpy : x.playerY=y.playerY)
    (hm : ∀ p,p∈x.patches ↔ p∈y.patches) (p : ℕ×ℕ) : tile (x,p)=tile (y,p) := by
  unfold tile
  rw [flag_ext x y hm Encoding.Tile.wall p,flag_ext x y hm Encoding.Tile.goal p,
    flag_ext x y hm Encoding.Tile.box p,hpx,hpy]

/-- Patch reordering and duplicate wall collars preserve every actual emitted cell. -/
theorem emit_ext (x y : Input) (hw : x.width=y.width) (hh : x.height=y.height)
    (hpx : x.playerX=y.playerX) (hpy : x.playerY=y.playerY) (hm : ∀ p,p∈x.patches ↔ p∈y.patches) :
    emit x=emit y := by
  unfold emit
  rw [hw,hh]
  congr 1
  apply List.map_congr_left
  intro row _
  apply List.map_congr_left
  intro col _
  exact tile_ext x y hpx hpy hm (col,row)

end PushPuzzle.PushFS.Reduction.Bitmap
