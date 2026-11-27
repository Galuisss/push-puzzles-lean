/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalBitmap

/-! Actual complete storage glyphs selected by the source cell compiler. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles


open Cslib.Complexity.NCL Gadgets.Wires PhysicalBitmap

abbrev Key := GateTileState ⊕ Catalog.Bitmap.Args

def key : CellPlan.Code→Option Key
  | none=>none
  | some (.inl g)=>some (.inl g.2)
  | some (.inr w)=>some (.inr w.2)

def Labels : Key→Type
  | .inl g=>(i : Fin (Fintype.card (GateTileRouting.Inventory.Index g)))×GateTileRouting.Inventory.AtlasLabels g i
  | .inr q=>(_i : Fin 1)×Catalog.Labels q.1

noncomputable instance (k : Key) : Fintype (Labels k) := by
  cases k <;> unfold Labels <;> infer_instance

noncomputable def piece : Key→Instance
  | .inl g=>GateTileRouting.fullPuzzle g
  | .inr q=>Catalog.puzzle q.1 q.2.1 q.2.2

noncomputable def matching : (k : Key)→SlotMatching (piece k) (Labels k)
  | .inl g=>GateTileRouting.fullSlotMatching g
  | .inr q=>Catalog.slotMatching q.1 q.2.1 q.2.2

def pad : Key→ℕ
  | .inl _=>0
  | .inr _=>1

def dimensions : Key→ℕ×ℕ
  | .inl _=>(200007,198068)
  | .inr _=>(200005,198066)

theorem piece_dimensions (k : Key) : (piece k).width=(dimensions k).1 ∧ (piece k).height=(dimensions k).2 := by
  cases k <;> exact ⟨rfl,rfl⟩

theorem padded_dimensions (k : Key) :
    pad k+(piece k).width≤strideX+7 ∧ pad k+(piece k).height≤strideY+7 := by
  rw [(piece_dimensions k).1,(piece_dimensions k).2]
  cases k <;> norm_num [pad,dimensions]

def offset (p : GridRouting.Point) (k : Key) : ℕ×ℕ :=
  (strideX*p.1+pad k,strideY*p.2+pad k)

theorem fits (w : Word) (p : Raster.Cell w) (k : Key) :
    (offset (p.1.val,p.2.val) k).1+(piece k).width≤strideX*Raster.width w+7 ∧
    (offset (p.1.val,p.2.val) k).2+(piece k).height≤strideY*Raster.height w+7 := by
  have hd := padded_dimensions k
  have hx := Nat.mul_le_mul_left strideX (Nat.succ_le_of_lt p.1.isLt)
  have hy := Nat.mul_le_mul_left strideY (Nat.succ_le_of_lt p.2.isLt)
  simp only [Nat.mul_succ] at hx hy
  dsimp only [offset]
  constructor <;> omega

/-- The machine patch at each true gate is exactly its complete semantic instance. -/
theorem gate_patch (p : GridRouting.Point) (g : CellPlan.Gate) :
    gatePatch (p,g)=Bitmap.instancePatch (piece (.inl g.2)) (offset p (.inl g.2)).1 (offset p (.inl g.2)).2 := by
  unfold gatePatch Bitmap.instancePatch offset piece pad
  rw [GateTileRouting.full_data]
  simp only [Nat.add_zero]

/-- Ordinary patches retain all physical boxes and targets of their actual seven-glyph instance. -/
theorem wire_patch (p : GridRouting.Point) (w : CellPlan.Wire) :
    wirePatch (p,w)=Bitmap.instancePatch (piece (.inr w.2)) (offset p (.inr w.2)).1 (offset p (.inr w.2)).2 := by
  unfold wirePatch Bitmap.instancePatch offset piece pad
  rw [Catalog.Bitmap.data_eq]

end PushPuzzle.PushFS.Reduction.PhysicalTiles
