/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.StorageAtlas
public import PushFS.Reduction.PlacedBitmap

/-!
# The actual atlas puzzle and its complete emitted bitmap

The rasterizer preserves every glyph's walls, initial boxes and goals. Its one
global player marker agrees with the semantic atlas. Thus the actual puzzle
is the machine output whenever its explicit patch list is polynomial time.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.StorageAtlas


open Turing.MultiTapeTM
open scoped Classical

variable {n W H : ℕ} {Label : Fin n → Type} [∀ i, Fintype (Label i)]

/-- Every concrete glyph's dense bitmap at its literal atlas offset. -/
def input (A : StorageAtlas n W H Label) : Bitmap.Input :=
  ⟨W, H, A.player.1.val, A.player.2.val, List.ofFn fun i =>
    Bitmap.instancePatch (A.piece i) (A.dx i) (A.dy i)⟩

private theorem flag_truth (A : StorageAtlas n W H Label) (p : Cell W H)
    (select : Encoding.Tile → Bool) (hempty : select Bitmap.emptyTile = false) :
    Bitmap.flag select (A.input, p.1.val, p.2.val) = true ↔
      ∃ i q, (A.embedding i).cells q = p ∧
        select (Encoding.tile (A.piece i).board (A.piece i).initial q) = true := by
  simp only [Bitmap.flag, input, List.any_eq_true, List.mem_ofFn]
  constructor
  · rintro ⟨patch, ⟨i, rfl⟩, hp⟩
    exact ⟨i, (Bitmap.instancePatch_truth (A.piece i) (A.dx i) (A.dy i)
      (A.fitsX i) (A.fitsY i) p select hempty).mp hp⟩
  · rintro ⟨i, hp⟩
    exact ⟨_, ⟨i, rfl⟩, (Bitmap.instancePatch_truth (A.piece i) (A.dx i) (A.dy i)
      (A.fitsX i) (A.fitsY i) p select hempty).mpr hp⟩

/-- Every emitted flag agrees with the actual complete global storage state. -/
theorem tile_eq (A : StorageAtlas n W H Label) (p : Cell W H) :
    Bitmap.tile (A.input, p.1.val, p.2.val) = Encoding.tile A.board A.initial p := by
  have hw : Bitmap.flag Encoding.Tile.wall (A.input, p.1.val, p.2.val) = decide (p ∈ A.board.walls) := by
    apply Bool.eq_iff_iff.mpr
    rw [flag_truth A p _ rfl]
    simp only [Encoding.tile, decide_eq_true_eq, board, walls, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_map]
    tauto
  have hg : Bitmap.flag Encoding.Tile.goal (A.input, p.1.val, p.2.val) = decide (p ∈ A.board.goals) := by
    apply Bool.eq_iff_iff.mpr
    rw [flag_truth A p _ rfl]
    simp only [Encoding.tile, decide_eq_true_eq]
    rw [A.mem_goals_iff p]
    tauto
  have hb : Bitmap.flag Encoding.Tile.box (A.input, p.1.val, p.2.val) = decide (p ∈ A.initial.boxes) := by
    apply Bool.eq_iff_iff.mpr
    rw [flag_truth A p _ rfl]
    simp only [Encoding.tile, decide_eq_true_eq]
    rw [A.mem_boxes_iff p]
    tauto
  have hp : decide (p.1.val = A.player.1.val ∧ p.2.val = A.player.2.val) = decide (p = A.player) := by
    simp only [Prod.ext_iff, Fin.ext_iff]
  change Encoding.Tile.mk _ _ _ _ = Encoding.Tile.mk _ _ _ _
  rw [hw, hg, hb]
  exact congrArg (Encoding.Tile.mk _ _ _) hp

/-- The complete dense output is exactly the actual atlas puzzle's fixed encoding data. -/
theorem data_eq (A : StorageAtlas n W H Label) : Encoding.data A.puzzle = Bitmap.emit A.input := by
  change Encoding.Data.mk W H (Encoding.rows A.board A.initial) =
    Encoding.Data.mk W H ((List.range H).map fun y => (List.range W).map fun x => Bitmap.tile (A.input, x, y))
  congr 1
  apply List.ext_getElem
  · simp only [Encoding.rows, List.length_ofFn, List.length_map, List.length_range]
  · intro y hy _
    have hy' : y < H := by simpa only [Encoding.rows, List.length_ofFn] using hy
    simp only [Encoding.rows, List.getElem_ofFn, List.getElem_map, List.getElem_range]
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_map, List.length_range]
    · intro x hx _
      have hx' : x < W := by simpa only [List.length_ofFn] using hx
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      exact (A.tile_eq (⟨x, hx'⟩, ⟨y, hy'⟩)).symm

end PushPuzzle.PushFS.Reduction.StorageAtlas
