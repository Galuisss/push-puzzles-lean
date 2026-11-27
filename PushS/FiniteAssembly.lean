/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Reduction.CellPlan

/-! Standard polynomial-time assembly of any fixed finite gate and wire bitmap table. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteAssembly

open PushFS PushFS.Reduction Gadgets.Wires
open Turing.MultiTapeTM ComputableInPolyTime
open Cslib.Complexity.NCL
open scoped Bitmap

/-- A fixed-force tile table and its shared physical placement lattice. -/
structure TileTable where
  /-- Complete gate bitmaps indexed by the actual source phase and cyclic port data. -/
  gate : GateTileState → Encoding.Data
  /-- Complete wire bitmaps indexed by actual direction and endpoint phases. -/
  wire : Catalog.Bitmap.Args → Encoding.Data
  /-- Horizontal and vertical spacing of neighboring source macrocells. -/
  stride : ℕ
  /-- Extra rectangle size containing the overlapping last collars. -/
  margin : ℕ

namespace TileTable

variable (T : TileTable)

/-- The actual patch emitted for a nonempty numbered source cell. -/
def patch (q : GridRouting.Point × CellPlan.Code) : Option Bitmap.Patch :=
  q.2.map fun c => ⟨T.stride*q.1.1, T.stride*q.1.2,
    c.elim (fun g => T.gate g.2) (fun w => T.wire w.2)⟩

private theorem patch_polyTime : ComputableInPolyTime T.patch
    (encPair Bitmap.encPoint CellPlan.encCode) (encOption Bitmap.encPatch) := by
  have hg : ComputableInPolyTime T.gate encGateTileState Encoding.encData := of_finite _
  have hw : ComputableInPolyTime T.wire Catalog.Bitmap.encArgs Encoding.encData := of_finite _
  have hs : ComputableInPolyTime
      (fun c : CellPlan.Gate ⊕ CellPlan.Wire =>
        c.elim (fun g => T.gate g.2) (fun w => T.wire w.2))
      (encSum CellPlan.encGate CellPlan.encWire) Encoding.encData := by fun_prop
  unfold patch
  fun_prop

/-- Empty source cells contribute no patch. -/
def patchList (q : GridRouting.Point × CellPlan.Code) : List Bitmap.Patch :=
  (T.patch q).elim [] fun p => [p]

private theorem patchList_polyTime : ComputableInPolyTime T.patchList
    (encPair Bitmap.encPoint CellPlan.encCode) (encList Bitmap.encPatch) := by
  have hp := patch_polyTime T
  unfold patchList
  fun_prop

/-- Render precisely the actual source rectangle's nonempty cells. -/
def patches (q : CellPlan.Source) : List Bitmap.Patch :=
  (CellPlan.cells q).flatMap (patchList T)

private theorem patches_polyTime : ComputableInPolyTime T.patches CellPlan.encSource
    (encList Bitmap.encPatch) := by
  have hc := CellPlan.cells_polyTime
  have hp := patchList_polyTime T
  unfold patches
  fun_prop

/-- One explicit physical rectangle and one exterior player for the complete source. -/
def input (q : CellPlan.Source) : Bitmap.Input :=
  ⟨T.stride*Raster.width q.1+T.margin, T.stride*Raster.height q.1+T.margin,
    0, 0, T.patches q⟩

theorem input_polyTime : ComputableInPolyTime T.input CellPlan.encSource Bitmap.encInput := by
  have hw := Raster.width_polyTime
  have hh := Raster.height_polyTime
  have hp := T.patches_polyTime
  unfold input
  fun_prop

/-- The complete dense output retains every wall, goal and working box. -/
def data (q : CellPlan.Source) : Encoding.Data := Bitmap.emit (T.input q)

theorem data_polyTime : ComputableInPolyTime T.data CellPlan.encSource Encoding.encData :=
  Bitmap.emit_polyTime.comp T.input_polyTime

end TileTable

/-- A finite table of actual primitive patches inside each source macrocell. -/
structure PrimitiveTable where
  gate : GateTileState → List Bitmap.Patch
  wire : Catalog.Bitmap.Args → List Bitmap.Patch
  stride : ℕ
  margin : ℕ

namespace PrimitiveTable

variable (T : PrimitiveTable)

def localPatches (c : CellPlan.Code) : List Bitmap.Patch :=
  c.elim [] fun code => code.elim (fun g => T.gate g.2) (fun w => T.wire w.2)

private theorem localPatches_polyTime : ComputableInPolyTime T.localPatches
    CellPlan.encCode (encList Bitmap.encPatch) := by
  have hg : ComputableInPolyTime T.gate encGateTileState (encList Bitmap.encPatch) := of_finite _
  have hw : ComputableInPolyTime T.wire Catalog.Bitmap.encArgs (encList Bitmap.encPatch) := of_finite _
  unfold localPatches
  fun_prop

/-- The original primitive bitmap with the actual source macrocell offset added once. -/
def placedPatch (q : GridRouting.Point × Bitmap.Patch) : Bitmap.Patch :=
  ⟨T.stride*q.1.1+q.2.x, T.stride*q.1.2+q.2.y, q.2.bitmap⟩

private theorem placedPatch_polyTime : ComputableInPolyTime T.placedPatch
    (encPair Bitmap.encPoint Bitmap.encPatch) Bitmap.encPatch := by
  unfold placedPatch
  fun_prop

def entryPatches (q : GridRouting.Point × CellPlan.Code) : List Bitmap.Patch :=
  (T.localPatches q.2).map fun p => T.placedPatch (q.1,p)

private theorem entryPatches_polyTime : ComputableInPolyTime T.entryPatches
    (encPair Bitmap.encPoint CellPlan.encCode) (encList Bitmap.encPatch) := by
  have hl := localPatches_polyTime T
  have hp := placedPatch_polyTime T
  unfold entryPatches
  fun_prop

/-- Flatten the complete actual primitive inventories of the source-cell plan. -/
def patches (q : CellPlan.Source) : List Bitmap.Patch :=
  (CellPlan.cells q).flatMap T.entryPatches

private theorem patches_polyTime : ComputableInPolyTime T.patches CellPlan.encSource
    (encList Bitmap.encPatch) := by
  have hc := CellPlan.cells_polyTime
  have hp := entryPatches_polyTime T
  unfold patches
  fun_prop

def input (q : CellPlan.Source) : Bitmap.Input :=
  ⟨T.stride*Raster.width q.1+T.margin, T.stride*Raster.height q.1+T.margin,
    0,0,T.patches q⟩

theorem input_polyTime : ComputableInPolyTime T.input CellPlan.encSource Bitmap.encInput := by
  have hw := Raster.width_polyTime
  have hh := Raster.height_polyTime
  have hp := T.patches_polyTime
  unfold input
  fun_prop

def data (q : CellPlan.Source) : Encoding.Data := Bitmap.emit (T.input q)

/-- The flattened actual primitive rendering has a standard polynomial-time machine. -/
theorem data_polyTime : ComputableInPolyTime T.data CellPlan.encSource Encoding.encData :=
  Bitmap.emit_polyTime.comp T.input_polyTime

end PrimitiveTable
end PushPuzzle.PushS.FiniteAssembly
