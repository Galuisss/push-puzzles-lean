/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalInterior

/-! Deep two-phase slots preserve coordinate order against every different physical macrocell. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open PhysicalBitmap
set_option maxHeartbeats 100000
attribute [local irreducible] Raster.width Raster.height

theorem inner_order_x (v : CellPlan.Source) (i j : Index v) (hij : i≠j)
    (p p' : Cell (PhysicalTiles.piece (tile i)).width (PhysicalTiles.piece (tile i)).height)
    (q q' : Cell (PhysicalTiles.piece (tile j)).width (PhysicalTiles.piece (tile j)).height)
    (hp : PhysicalTiles.Inner (tile i) p) (hp' : PhysicalTiles.Inner (tile i) p')
    (hy : (PhysicalTiles.coordinates (position i) (tile i) p).2=
      (PhysicalTiles.coordinates (position j) (tile j) q).2) :
    ((PhysicalTiles.coordinates (position i) (tile i) p).1<
        (PhysicalTiles.coordinates (position j) (tile j) q).1 ↔
      (PhysicalTiles.coordinates (position i) (tile i) p').1<
        (PhysicalTiles.coordinates (position j) (tile j) q').1) ∧
    ((PhysicalTiles.coordinates (position j) (tile j) q).1<
        (PhysicalTiles.coordinates (position i) (tile i) p).1 ↔
      (PhysicalTiles.coordinates (position j) (tile j) q').1<
        (PhysicalTiles.coordinates (position i) (tile i) p').1) := by
  have hq:=PhysicalTiles.coordinate_bounds (position j) (tile j) q
  have hq':=PhysicalTiles.coordinate_bounds (position j) (tile j) q'
  have he : (position i).2=(position j).2 := by
    dsimp only [PhysicalTiles.Inner,PhysicalTiles.coordinates,PhysicalTiles.offset,strideX,strideY] at hp hq hy
    omega
  have hn : (position i).1≠(position j).1 := by
    intro hx
    exact hij (position_injective (Prod.ext hx he))
  dsimp only [PhysicalTiles.Inner,PhysicalTiles.coordinates,PhysicalTiles.offset,strideX,strideY] at hp hp' hq hq' ⊢
  constructor <;> constructor <;> intro hh <;> omega

theorem inner_order_y (v : CellPlan.Source) (i j : Index v) (hij : i≠j)
    (p p' : Cell (PhysicalTiles.piece (tile i)).width (PhysicalTiles.piece (tile i)).height)
    (q q' : Cell (PhysicalTiles.piece (tile j)).width (PhysicalTiles.piece (tile j)).height)
    (hp : PhysicalTiles.Inner (tile i) p) (hp' : PhysicalTiles.Inner (tile i) p')
    (hx : (PhysicalTiles.coordinates (position i) (tile i) p).1=
      (PhysicalTiles.coordinates (position j) (tile j) q).1) :
    ((PhysicalTiles.coordinates (position i) (tile i) p).2<
        (PhysicalTiles.coordinates (position j) (tile j) q).2 ↔
      (PhysicalTiles.coordinates (position i) (tile i) p').2<
        (PhysicalTiles.coordinates (position j) (tile j) q').2) ∧
    ((PhysicalTiles.coordinates (position j) (tile j) q).2<
        (PhysicalTiles.coordinates (position i) (tile i) p).2 ↔
      (PhysicalTiles.coordinates (position j) (tile j) q').2<
        (PhysicalTiles.coordinates (position i) (tile i) p').2) := by
  have hq:=PhysicalTiles.coordinate_bounds (position j) (tile j) q
  have hq':=PhysicalTiles.coordinate_bounds (position j) (tile j) q'
  have he : (position i).1=(position j).1 := by
    dsimp only [PhysicalTiles.Inner,PhysicalTiles.coordinates,PhysicalTiles.offset,strideX,strideY] at hp hq hx
    omega
  have hn : (position i).2≠(position j).2 := by
    intro hy
    exact hij (position_injective (Prod.ext he hy))
  dsimp only [PhysicalTiles.Inner,PhysicalTiles.coordinates,PhysicalTiles.offset,strideX,strideY] at hp hp' hq hq' ⊢
  constructor <;> constructor <;> intro hh <;> omega

end PushPuzzle.PushFS.Reduction.PhysicalInventory
