/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalProfileForeign
public import PushFS.Reduction.FullGateOuterFrame
public import PushFS.Gadgets.Wires.Catalog.ExteriorGeometry
public import PushFS.Reduction.MeshWalking

/-! Shared literal macrocell corners on the actual whole physical source board. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL PhysicalBitmap Gadgets.Wires
set_option maxRecDepth 65536
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

def cornerX (i : Fin 4) : ℕ := if i.val%2=0 then 1 else 200005
def cornerY (i : Fin 4) : ℕ := if i.val<2 then 1 else 198066

def macroCorner (w : Word) (p : Raster.Cell w) (i : Fin 4) :
    Cell (strideX*Raster.width w+7) (strideY*Raster.height w+7) :=
  (⟨strideX*p.1.val+cornerX i,by
    have hx:=Nat.mul_le_mul_left strideX (Nat.succ_le_of_lt p.1.isLt)
    rw [Nat.mul_succ] at hx
    have hc : cornerX i≤200005 := by unfold cornerX; split <;> omega
    dsimp only [strideX] at hx ⊢
    omega⟩,
   ⟨strideY*p.2.val+cornerY i,by
    have hy:=Nat.mul_le_mul_left strideY (Nat.succ_le_of_lt p.2.isLt)
    rw [Nat.mul_succ] at hy
    have hc : cornerY i≤198066 := by unfold cornerY; split <;> omega
    dsimp only [strideY] at hy ⊢
    omega⟩)

def meshPoint (w : Word) (p : Raster.Cell w) := macroCorner w p 0

def nativeCorner : (k : PhysicalTiles.Key)→Fin 4→Cell (PhysicalTiles.piece k).width (PhysicalTiles.piece k).height
  | .inl _,i=>GateTileRouting.outerCorner i
  | .inr _,i=>Catalog.outerCorner i

private theorem corner_coordinates (p : GridRouting.Point) (k : PhysicalTiles.Key) (i : Fin 4) :
    PhysicalTiles.coordinates p k (nativeCorner k i)=
      (strideX*p.1+cornerX i,strideY*p.2+cornerY i) := by
  cases k <;> fin_cases i <;>
    simp [nativeCorner,GateTileRouting.outerCorner,Catalog.outerCorner,PhysicalTiles.coordinates,
      PhysicalTiles.offset,PhysicalTiles.pad,cornerX,cornerY,Nat.add_assoc]

theorem embedding_corner (v : CellPlan.Source) (i : Index v) (j : Fin 4) :
    (embedding v i).cells (nativeCorner (tile i) j)=macroCorner v.1 i.val.1 j := by
  have he:=corner_coordinates (position i) (tile i) j
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

end PushPuzzle.PushFS.Reduction.PhysicalInventory
