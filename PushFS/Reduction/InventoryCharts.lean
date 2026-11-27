/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Reduction.InventoryAssembly
public import PushFS.AxisStencil

/-! Place actual local wall stencils in a literal inventory wall union. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.InventoryAssembly

variable {n W H : ℕ} {Label : Fin n → Type} [∀ i, Fintype (Label i)]

def placedChart (A : InventoryAssembly n W H Label) (i : Fin n)
    (C : TranslatedAxisChart (A.piece i).width (A.piece i).height) : TranslatedAxisChart W H where
  width := C.width
  height := C.height
  board := C.board
  dx := A.dx i+C.dx
  dy := A.dy i+C.dy
  fits_x := by have := C.fits_x; have := A.fitsX i; omega
  fits_y := by have := C.fits_y; have := A.fitsY i; omega
  classifier := C.classifier

theorem placedChart_cells (A : InventoryAssembly n W H Label) (i : Fin n)
    (C : TranslatedAxisChart (A.piece i).width (A.piece i).height) (p : Cell C.width C.height) :
    (A.placedChart i C).embedding.cells p = (A.embedding i).cells (C.embedding.cells p) := by
  apply Prod.ext <;> apply Fin.ext
  · change A.dx i+C.dx+p.1.val = A.dx i+(C.dx+p.1.val)
    omega
  · change A.dy i+C.dy+p.2.val = A.dy i+(C.dy+p.2.val)
    omega

/-- Only the local protecting walls, with no whole-rectangle agreement, are used. -/
theorem placedChart_walls (A : InventoryAssembly n W H Label) (i : Fin n)
    (C : TranslatedAxisChart (A.piece i).width (A.piece i).height)
    (hw : ∀ p, p ∈ C.board.walls → C.embedding.cells p ∈ (A.piece i).board.walls)
    (p : Cell C.width C.height) (hp : p ∈ C.board.walls) :
    (A.placedChart i C).embedding.cells p ∈ A.walls := by
  rw [A.placedChart_cells i C p]
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_map.mpr ⟨C.embedding.cells p,hw p hp,rfl⟩⟩

end PushPuzzle.PushFS.Reduction.InventoryAssembly
