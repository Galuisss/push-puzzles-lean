/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateTracks
public import PushFS.GuardStencils

/-! Actual protecting junction stencils inside the parameterized thick gate cores. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateStencils

open PushFS FiniteGeometry FiniteGateCore

attribute [local irreducible] side

/-- The AND row/B-column window, with a complete bottom guard and B's right guard. -/
def andJunction (w : ℕ) : TranslatedAxisChart (side w) (side w) where
  width := 12*w+33
  height := 10*w+43
  board := GuardStencils.junctionBoard (⟨7*w+12, by omega⟩ : Fin (12*w+33))
    (⟨10*w+41, by omega⟩ : Fin (10*w+43))
  dx := origin w-7*w-9
  dy := origin w-10*w-41
  fits_x := by unfold origin side; omega
  fits_y := by unfold origin side; omega
  classifier := GuardStencils.junctionClassifier _ _

/-- The OR window keeps exactly the same monotone vertical-to-horizontal junction pattern. -/
def orJunction (w : ℕ) : TranslatedAxisChart (side w) (side w) where
  width := 9*w+42
  height := 4*w+25
  board := GuardStencils.junctionBoard (⟨4*w+21, by omega⟩ : Fin (9*w+42))
    (⟨4*w+23, by omega⟩ : Fin (4*w+25))
  dx := origin w-4*w-17
  dy := origin w-4*w-23
  fits_x := by unfold origin side; omega
  fits_y := by unfold origin side; omega
  classifier := GuardStencils.junctionClassifier _ _

/-- All minimal AND junction guards are among the seven actual wall rectangles. -/
theorem andJunction_walls (w : ℕ) (hw : 2 ≤ w) (p : Cell (andJunction w).width (andJunction w).height)
    (hp : p ∈ (andJunction w).board.walls) : (andJunction w).embedding.cells p ∈ andWalls w := by
  change p ∈ (Finset.univ.filter fun q : Cell (12*w+33) (10*w+43) =>
    q.2.val = (10*w+41)+1 ∨ (q.1.val = (7*w+12)+1 ∧ q.2.val < 10*w+41)) at hp
  have hp' := (Finset.mem_filter.mp hp).2
  have hpx := p.1.isLt
  have hpy := p.2.isLt
  have hX : ((andJunction w).embedding.cells p).1.val = origin w-7*w-9+p.1.val := rfl
  have hY : ((andJunction w).embedding.cells p).2.val = origin w-10*w-41+p.2.val := rfl
  rcases hp' with hy | ⟨hx, hy⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨0, Finset.mem_univ _, ?_⟩
    apply (Rectangle.mem_cells (andRectangle w 0) _ _ _).mpr
    rw [hX, hY]
    simp [andRectangle, andJunction, origin] at *
    omega
  · apply Finset.mem_biUnion.mpr
    refine ⟨6, Finset.mem_univ _, ?_⟩
    apply (Rectangle.mem_cells (andRectangle w 6) _ _ _).mpr
    rw [hX, hY]
    simp [andRectangle, andJunction, origin] at *
    omega

theorem orJunction_walls (w : ℕ) (hw : 2 ≤ w) (p : Cell (orJunction w).width (orJunction w).height)
    (hp : p ∈ (orJunction w).board.walls) : (orJunction w).embedding.cells p ∈ orWalls w := by
  change p ∈ (Finset.univ.filter fun q : Cell (9*w+42) (4*w+25) =>
    q.2.val = (4*w+23)+1 ∨ (q.1.val = (4*w+21)+1 ∧ q.2.val < 4*w+23)) at hp
  have hp' := (Finset.mem_filter.mp hp).2
  have hpx := p.1.isLt
  have hpy := p.2.isLt
  have hX : ((orJunction w).embedding.cells p).1.val = origin w-4*w-17+p.1.val := rfl
  have hY : ((orJunction w).embedding.cells p).2.val = origin w-4*w-23+p.2.val := rfl
  rcases hp' with hy | ⟨hx, hy⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨0, Finset.mem_univ _, ?_⟩
    apply (Rectangle.mem_cells (orRectangle w 0) _ _ _).mpr
    rw [hX, hY]
    simp [orRectangle, orJunction, origin] at *
    omega
  · apply Finset.mem_biUnion.mpr
    refine ⟨1, Finset.mem_univ _, ?_⟩
    apply (Rectangle.mem_cells (orRectangle w 1) _ _ _).mpr
    rw [hX, hY]
    simp [orRectangle, orJunction, origin] at *
    omega

/-- The full actual AND wall restriction has the same guarded local displacement names. -/
def andActualJunction (w : ℕ) (hw : 2 ≤ w) (goals : Finset (Cell (side w) (side w))) :
    TranslatedAxisChart (side w) (side w) :=
  (andJunction w).restrictToFloor (andBoard w goals) (andJunction_walls w hw)

def orActualJunction (w : ℕ) (hw : 2 ≤ w) (goals : Finset (Cell (side w) (side w))) :
    TranslatedAxisChart (side w) (side w) :=
  (orJunction w).restrictToFloor (orBoard w goals) (orJunction_walls w hw)

end PushPuzzle.PushS.FiniteGateStencils
