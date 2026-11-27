/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.StaticPlacement

/-! Translated finite wall stencils and their axis coordinates. -/

@[expose] public section

namespace PushPuzzle.PushFS

namespace AxisTrack

/-- Translate a row, column or singleton coordinate name. -/
def shift (dx dy : ℕ) : AxisTrack → AxisTrack
  | .outside => .outside
  | .horizontal y => .horizontal (dy + y)
  | .vertical x => .vertical (dx + x)
  | .sink x y => .sink (dx + x) (dy + y)

@[simp] theorem level_shift (dx dy : ℕ) (t : AxisTrack) : (shift dx dy t).level = t.level := by
  cases t <;> rfl

theorem shift_injective (dx dy : ℕ) : Function.Injective (shift dx dy) := by
  intro a b he
  cases a <;> cases b <;> simp_all [shift]

/-- Coordinate support remains literal coordinate support after translation. -/
theorem shift_supported {w h W H : ℕ} (dx dy : ℕ) (hx : dx + w ≤ W) (hy : dy + h ≤ H)
    {p : Cell w h} {t : AxisTrack} (ht : t.Supports p) :
    (shift dx dy t).Supports ((GridEmbedding.translate dx dy hx hy).cells p) := by
  cases t <;> simp_all [shift, AxisTrack.Supports, GridEmbedding.translate]

end AxisTrack

/-- One finite wall stencil placed by translation inside the full board. -/
structure TranslatedAxisChart (W H : ℕ) where
  /-- Finite stencil width. -/
  width : ℕ
  /-- Finite stencil height. -/
  height : ℕ
  /-- The exact finite source walls. -/
  board : Board width height
  /-- Horizontal translation offset. -/
  dx : ℕ
  /-- Vertical translation offset. -/
  dy : ℕ
  /-- The whole stencil fits horizontally. -/
  fits_x : dx + width ≤ W
  /-- The whole stencil fits vertically. -/
  fits_y : dy + height ≤ H
  /-- The actual finite-board axis classifier. -/
  classifier : AxisClassifier board

/-- The chart's rectangle embedding. -/
def TranslatedAxisChart.embedding {W H : ℕ} (C : TranslatedAxisChart W H) :
    GridEmbedding C.width C.height W H :=
  GridEmbedding.translate C.dx C.dy C.fits_x C.fits_y

end PushPuzzle.PushFS
