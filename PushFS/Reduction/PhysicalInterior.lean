/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalStatics

/-! Deep macrocell points keep their precise local axis names on the complete board. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.PhysicalTiles

open PhysicalBitmap

def Inner (k : Key) (q : Cell (piece k).width (piece k).height) : Prop :=
  7≤pad k+q.1.val ∧pad k+q.1.val<strideX ∧7≤pad k+q.2.val ∧pad k+q.2.val<strideY

end PushPuzzle.PushFS.Reduction.PhysicalTiles

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory
open PhysicalBitmap Gadgets.Wires GateTileRouting.FullGateStatics
set_option maxHeartbeats 100000
set_option maxRecDepth 65536
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

private theorem inner_owner (v : CellPlan.Source) (i j : Index v)
    (q : Cell (PhysicalTiles.piece (tile i)).width (PhysicalTiles.piece (tile i)).height)
    (s : Cell (PhysicalTiles.piece (tile j)).width (PhysicalTiles.piece (tile j)).height)
    (hq : PhysicalTiles.Inner (tile i) q)
    (he : (axisChart v j).embedding.cells s=(axisChart v i).embedding.cells q) : i=j := by
  have hb:=PhysicalTiles.coordinate_bounds (position j) (tile j) s
  have hx:=congrArg (fun p : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)=>p.1.val) he
  have hy:=congrArg (fun p : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)=>p.2.val) he
  change (PhysicalTiles.coordinates (position j) (tile j) s).1=
    (PhysicalTiles.coordinates (position i) (tile i) q).1 at hx
  change (PhysicalTiles.coordinates (position j) (tile j) s).2=
    (PhysicalTiles.coordinates (position i) (tile i) q).2 at hy
  rw [hx,hy] at hb
  have hp : position i=position j := by
    apply Prod.ext
    all_goals dsimp only [PhysicalTiles.Inner,PhysicalTiles.coordinates,PhysicalTiles.offset,strideX,strideY] at hq hb
    all_goals omega
  exact position_injective hp

theorem inner_name (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Index v) (q : Cell (PhysicalTiles.piece (tile i)).width (PhysicalTiles.piece (tile i)).height)
    (hq : PhysicalTiles.Inner (tile i) q) (ha : (PhysicalTiles.classifier (tile i)).name q≠.outside) :
    (axisClassifier v hP hT).name ((axisChart v i).embedding.cells q)=
      AxisTrack.shift (axisChart v i).dx (axisChart v i).dy ((PhysicalTiles.classifier (tile i)).name q) := by
  have hactive:=(axisMosaic v hP hT).source_active i q ha
  obtain ⟨j,s,he,hn⟩:=(axisMosaic v hP hT).attained _ hactive
  change (axisChart v j).embedding.cells s=(axisChart v i).embedding.cells q at he
  have hij:=inner_owner v i j q s hq he
  subst j
  have hs:=(axisChart v i).embedding.cells.injective he
  subst s
  exact hn.symm

theorem full_core_inner (g : GateTileState) (p : Gadgets.Gates.C) :
    PhysicalTiles.Inner (.inl g) ((chart g (.inl (.inl 0))).embedding.cells p) := by
  have hx:=p.1.isLt
  have hy:=p.2.isLt
  change 7≤0+((GateTileRouting.bufferOffset g.core.isAND).1+2311+p.1.val) ∧
    0+((GateTileRouting.bufferOffset g.core.isAND).1+2311+p.1.val)<200000 ∧
    7≤0+((GateTileRouting.bufferOffset g.core.isAND).2+2321+p.2.val) ∧
    0+((GateTileRouting.bufferOffset g.core.isAND).2+2321+p.2.val)<198061
  cases g.core.isAND
  · change 7≤0+(99959+p.1.val) ∧0+(99959+p.1.val)<200000 ∧
      7≤0+(98974+p.2.val) ∧0+(98974+p.2.val)<198061
    omega
  · change 7≤0+(99960+p.1.val) ∧0+(99960+p.1.val)<200000 ∧
      7≤0+(98974+p.2.val) ∧0+(98974+p.2.val)<198061
    omega

end PushPuzzle.PushFS.Reduction.PhysicalInventory
