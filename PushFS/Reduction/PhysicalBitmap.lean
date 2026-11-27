/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.CellPlan
public import PushFS.Reduction.FullGateTile
public import PushFS.Gadgets.Wires.Catalog.Bitmap

/-! The complete source cell plan rendered as actual physical gate and wire bitmaps. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalBitmap


open Cslib.Complexity.NCL Turing.MultiTapeTM ComputableInPolyTime Gadgets.Wires
open scoped Bitmap

abbrev strideX : ℕ := 200000
abbrev strideY : ℕ := 198061
abbrev Entry := GridRouting.Point × CellPlan.Code
abbrev encEntry := encPair Bitmap.encPoint CellPlan.encCode

/-- Pad3 gates and pad2 wires share their actual logical boundary coordinates. -/
def gatePatch (q : GridRouting.Point × CellPlan.Gate) : Bitmap.Patch :=
  ⟨strideX*q.1.1,strideY*q.1.2,GateTileRouting.Inventory.data q.2.2⟩

def wirePatch (q : GridRouting.Point × CellPlan.Wire) : Bitmap.Patch :=
  ⟨strideX*q.1.1+1,strideY*q.1.2+1,Bitmap.emit (Catalog.Bitmap.recipe q.2.2)⟩

private theorem gatePatch_polyTime : ComputableInPolyTime gatePatch
    (encPair Bitmap.encPoint CellPlan.encGate) Bitmap.encPatch := by
  have hd := GateTileRouting.Inventory.data_polyTime
  unfold gatePatch
  fun_prop

private theorem wirePatch_polyTime : ComputableInPolyTime wirePatch
    (encPair Bitmap.encPoint CellPlan.encWire) Bitmap.encPatch := by
  have hr := Catalog.Bitmap.recipe_polyTime
  have he := Bitmap.emit_polyTime
  unfold wirePatch
  fun_prop

def patch (q : Entry) : Option Bitmap.Patch :=
  q.2.elim none fun c => c.elim (fun g=>some (gatePatch (q.1,g))) (fun w=>some (wirePatch (q.1,w)))

private theorem patch_polyTime : ComputableInPolyTime patch encEntry
    (encOption Bitmap.encPatch) := by
  have hv : ComputableInPolyTime (fun q : Entry=>q.2) encEntry CellPlan.encCode := by fun_prop
  have hg : ComputableInPolyTime (fun q : (Entry × (CellPlan.Gate ⊕ CellPlan.Wire)) × CellPlan.Gate=>
      some (gatePatch (q.1.1.1,q.2)))
      (encPair (encPair encEntry (encSum CellPlan.encGate CellPlan.encWire)) CellPlan.encGate)
      (encOption Bitmap.encPatch) := by
    have hh := gatePatch_polyTime
    fun_prop
  have hw : ComputableInPolyTime (fun q : (Entry × (CellPlan.Gate ⊕ CellPlan.Wire)) × CellPlan.Wire=>
      some (wirePatch (q.1.1.1,q.2)))
      (encPair (encPair encEntry (encSum CellPlan.encGate CellPlan.encWire)) CellPlan.encWire)
      (encOption Bitmap.encPatch) := by
    have hh := wirePatch_polyTime
    fun_prop
  have hs : ComputableInPolyTime (fun q : Entry × (CellPlan.Gate ⊕ CellPlan.Wire)=>q.2)
      (encPair encEntry (encSum CellPlan.encGate CellPlan.encWire))
      (encSum CellPlan.encGate CellPlan.encWire) := by fun_prop
  exact hv.optionElimWithInput (const none) (hs.sumElimWithInput hg hw)

def patchList (q : Entry) : List Bitmap.Patch := (patch q).elim [] fun p=>[p]

private theorem patchList_polyTime : ComputableInPolyTime patchList encEntry
    (encList Bitmap.encPatch) := by
  have hs : ComputableInPolyTime (fun q : Entry × Bitmap.Patch=>[q.2])
      (encPair encEntry Bitmap.encPatch) (encList Bitmap.encPatch) := by fun_prop
  exact patch_polyTime.optionElimWithInput (const []) hs

/-- Every nonempty actual source cell contributes its complete physical storage inventory. -/
def patches (q : CellPlan.Source) : List Bitmap.Patch :=
  (CellPlan.cells q).flatMap patchList

private theorem patches_polyTime : ComputableInPolyTime patches CellPlan.encSource
    (encList Bitmap.encPatch) := by
  have hc := CellPlan.cells_polyTime
  have hp := patchList_polyTime
  unfold patches
  fun_prop

def input (q : CellPlan.Source) : Bitmap.Input :=
  ⟨strideX*Raster.width q.1+7,strideY*Raster.height q.1+7,1,1,patches q⟩

private theorem input_polyTime : ComputableInPolyTime input CellPlan.encSource Bitmap.encInput := by
  have hw := Raster.width_polyTime
  have hh := Raster.height_polyTime
  have hp := patches_polyTime
  unfold input
  fun_prop

/-- The full physical rectangle, including all auxiliary boxes, goals, walls and exterior floor. -/
def data (q : CellPlan.Source) : Encoding.Data := Bitmap.emit (input q)

theorem data_polyTime : ComputableInPolyTime data CellPlan.encSource Encoding.encData :=
  Bitmap.emit_polyTime.comp input_polyTime

theorem patch_gate (p : GridRouting.Point) (v : CellPlan.Gate) :
    patch (p,some (.inl v))=some (gatePatch (p,v)) := rfl

theorem patch_wire (p : GridRouting.Point) (w : CellPlan.Wire) :
    patch (p,some (.inr w))=some (wirePatch (p,w)) := rfl

end PushPuzzle.PushFS.Reduction.PhysicalBitmap
