/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Isometry
public import PushFS.Reduction.Bitmap
import Mathlib.Data.List.GetD

/-!
# Polynomial-time dense grid reorientation

Transposition and horizontal reflection inspect and emit every declared cell.
The resulting dense data agree exactly with the semantic grid isometries,
including the player marker, every physical box and the unlabelled goal set.
-/

@[expose] public section

namespace PushPuzzle.PushFS


open Turing.MultiTapeTM ComputableInPolyTime
open scoped Encoding

namespace Encoding

/-- The full rectangular transpose, using empty floor for malformed row lookups. -/
def Data.transpose (d : Data) : Data :=
  ⟨d.height, d.width, (List.range d.width).map fun y =>
    (List.range d.height).map fun x => (d.rows.getD x []).getD y Reduction.Bitmap.emptyTile⟩

/-- Reflect all four markers across the vertical center line of the declared rectangle. -/
def Data.reflectX (d : Data) : Data :=
  ⟨d.width, d.height, (List.range d.height).map fun y =>
    (List.range d.width).map fun x =>
      (d.rows.getD y []).getD (d.width - 1 - x) Reduction.Bitmap.emptyTile⟩

@[fun_prop] theorem Data.transpose_polyTime : ComputableInPolyTime Data.transpose encData encData := by
  unfold Data.transpose
  fun_prop

@[fun_prop] theorem Data.reflectX_polyTime : ComputableInPolyTime Data.reflectX encData encData := by
  unfold Data.reflectX
  fun_prop

/-- Looking up an in-bounds encoded cell returns its four actual semantic markers. -/
theorem lookup_rows {w h : ℕ} (B : Board w h) (s : State w h)
    (x y : ℕ) (hx : x < w) (hy : y < h) :
    ((rows B s).getD y []).getD x Reduction.Bitmap.emptyTile = tile B s (⟨x, hx⟩, ⟨y, hy⟩) := by
  simp [rows, List.getD_eq_getElem?_getD, hx, hy]

/-- Every flag is preserved at the corresponding isometric cell. -/
private theorem tile_isometry {w h W H : ℕ} (e : GridIsometry w h W H) (B : Board w h)
    (s : State w h) (p : Cell w h) : tile (e.board B) (e.state s) (e.cells p) = tile B s p := by
  simp [tile, GridIsometry.state]

/-- The actual transposed puzzle has exactly the machine-emitted dense transpose. -/
private theorem data_transpose (I : Instance) :
    data (GridIsometry.reorientInstance I (GridIsometry.transpose I.width I.height)) =
      (data I).transpose := by
  change Data.mk I.height I.width
      (rows ((GridIsometry.transpose I.width I.height).board I.board)
        ((GridIsometry.transpose I.width I.height).state I.initial)) =
    Data.mk I.height I.width ((List.range I.width).map fun y =>
      (List.range I.height).map fun x =>
        ((rows I.board I.initial).getD x []).getD y Reduction.Bitmap.emptyTile)
  congr 1
  apply List.ext_getElem
  · simp [rows]
  · intro y hy _
    have hy' : y < I.width := by simpa [rows] using hy
    simp only [rows, List.getElem_ofFn, List.getElem_map, List.getElem_range]
    apply List.ext_getElem
    · simp
    · intro x hx _
      have hx' : x < I.height := by simpa only [List.length_ofFn] using hx
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      change tile ((GridIsometry.transpose I.width I.height).board I.board)
        ((GridIsometry.transpose I.width I.height).state I.initial) (⟨x, hx'⟩, ⟨y, hy'⟩) =
        ((rows I.board I.initial).getD x []).getD y Reduction.Bitmap.emptyTile
      rw [lookup_rows I.board I.initial y x hy' hx']
      exact tile_isometry (GridIsometry.transpose I.width I.height) I.board I.initial
        (⟨y, hy'⟩, ⟨x, hx'⟩)

/-- The actual reflected puzzle has exactly the machine-emitted dense reflection. -/
private theorem data_reflectX (I : Instance) :
    data (GridIsometry.reorientInstance I (GridIsometry.reflectX I.width I.height)) =
      (data I).reflectX := by
  change Data.mk I.width I.height
      (rows ((GridIsometry.reflectX I.width I.height).board I.board)
        ((GridIsometry.reflectX I.width I.height).state I.initial)) =
    Data.mk I.width I.height ((List.range I.height).map fun y =>
      (List.range I.width).map fun x =>
        ((rows I.board I.initial).getD y []).getD (I.width - 1 - x) Reduction.Bitmap.emptyTile)
  congr 1
  apply List.ext_getElem
  · simp [rows]
  · intro y hy _
    have hy' : y < I.height := by simpa [rows] using hy
    simp only [rows, List.getElem_ofFn, List.getElem_map, List.getElem_range]
    apply List.ext_getElem
    · simp
    · intro x hx _
      have hx' : x < I.width := by simpa only [List.length_ofFn] using hx
      have hxrev : I.width - 1 - x < I.width := by omega
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      change tile ((GridIsometry.reflectX I.width I.height).board I.board)
        ((GridIsometry.reflectX I.width I.height).state I.initial) (⟨x, hx'⟩, ⟨y, hy'⟩) =
        ((rows I.board I.initial).getD y []).getD (I.width - 1 - x) Reduction.Bitmap.emptyTile
      rw [lookup_rows I.board I.initial (I.width - 1 - x) y hxrev hy']
      have he : (GridIsometry.reflectX I.width I.height).cells
          (⟨I.width - 1 - x, hxrev⟩, ⟨y, hy'⟩) = (⟨x, hx'⟩, ⟨y, hy'⟩) := by
        apply Prod.ext
        · apply Fin.ext
          change I.width - ((I.width - 1 - x) + 1) = x
          omega
        · rfl
      rw [← he]
      exact tile_isometry _ _ _ _

/-- Access to semantic dense data is the identity on the fixed instance encoding. -/
theorem data_polyTime : ComputableInPolyTime data encoding encData :=
  ComputableInPolyTime.of_eq (fun _ => rfl)

end Encoding

namespace Instance

/-- Transpose all four cell markers of a legal storage instance. -/
def transposed (I : Instance) : Instance :=
  GridIsometry.reorientInstance I (GridIsometry.transpose I.width I.height)

/-- Reflect all four cell markers of a legal storage instance. -/
def reflectedX (I : Instance) : Instance :=
  GridIsometry.reorientInstance I (GridIsometry.reflectX I.width I.height)

/-- Transposition has an actual multi-tape-machine polynomial-time implementation. -/
@[fun_prop] theorem transposed_polyTime : ComputableInPolyTime transposed encoding encoding :=
  (Encoding.Data.transpose_polyTime.comp Encoding.data_polyTime).of_enc_eq
    (fun I => congrArg Encoding.encData (Encoding.data_transpose I))

/-- Horizontal reflection has an actual multi-tape-machine polynomial-time implementation. -/
@[fun_prop] theorem reflectedX_polyTime : ComputableInPolyTime reflectedX encoding encoding :=
  (Encoding.Data.reflectX_polyTime.comp Encoding.data_polyTime).of_enc_eq
    (fun I => congrArg Encoding.encData (Encoding.data_reflectX I))

end Instance
end PushPuzzle.PushFS
