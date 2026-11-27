/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.SourceWireSelection
public import PushFS.Reduction.GateTileData
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-! Machine polynomial-time full cell instructions for the actual source word and both orientation bit lists. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.CellPlan


open Cslib.Complexity.NCL Plan Gadgets.Wires Turing.MultiTapeTM ComputableInPolyTime
open scoped PushPuzzle.PushFS.Reduction PushPuzzle.PushFS.Reduction.Plan

abbrev Source := Word × (List Bool × List Bool)
abbrev encSource : Source ↪ List Bool := encPair encWord (encPair (encList encBool) (encList encBool))
abbrev Gate := VertexData × GateTileState
abbrev Wire := ℕ × Catalog.Bitmap.Args
abbrev Code := Option (Gate ⊕ Wire)
abbrev encGate := encPair encVertexData encGateTileState
abbrev encWire := encPair encUnary Catalog.Bitmap.encArgs
abbrev encCode := encOption (encSum encGate encWire)
abbrev Query := Source × GridRouting.Point
abbrev encQuery := encPair encSource Bitmap.encPoint
abbrev WireQuery := Source × (ℕ × GridRouting.Point)
abbrev encWireQuery := encPair encSource (encPair encUnary Bitmap.encPoint)

/-- The actual original edge number and both complete canonical physical wire phases. -/
def wireData (q : WireQuery) : Option Wire :=
  (Raster.wireAt (q.1.1,(q.2.1,q.2.2))).map fun k =>
    (q.2.1,(k,!(q.1.2.1.getD q.2.1 false),!(q.1.2.2.getD q.2.1 false)))

private theorem wireData_polyTime : ComputableInPolyTime wireData encWireQuery
    (encOption encWire) := by
  have hw := Raster.wireAt_polyTime
  have hv : ComputableInPolyTime (fun q : WireQuery => Raster.wireAt (q.1.1,(q.2.1,q.2.2)))
      encWireQuery (encOption Catalog.encKind) := by fun_prop
  have hf : ComputableInPolyTime
      (fun q : WireQuery × Catalog.Kind => (q.1.2.1,(q.2,!(q.1.1.2.1.getD q.1.2.1 false),!(q.1.1.2.2.getD q.1.2.1 false))))
      (encPair encWireQuery Catalog.encKind) encWire := by fun_prop
  exact hv.optionMapWithInput hf

/-- An ordinary named source pixel selects the real finite physical wire glyph. -/
def ordinary (q : Query) : Code :=
  (Raster.owner (q.1.1,q.2)).elim none fun e =>
    (wireData (q.1,(e,q.2))).map Sum.inr

private theorem ordinary_polyTime : ComputableInPolyTime ordinary encQuery encCode := by
  have ho := Raster.owner_polyTime
  have hv : ComputableInPolyTime (fun q : Query => Raster.owner (q.1.1,q.2)) encQuery (encOption encUnary) := by fun_prop
  have hw : ComputableInPolyTime (fun q : Query × ℕ => wireData (q.1.1,(q.2,q.1.2)))
      (encPair encQuery encUnary) (encOption encWire) := by
    have hh := wireData_polyTime
    fun_prop
  have hb : ComputableInPolyTime (fun q : (Query × ℕ) × Wire => Sum.inr (α := Gate) q.2)
      (encPair (encPair encQuery encUnary) encWire) (encSum encGate encWire) := by fun_prop
  exact hv.optionElimWithInput (const none) (hw.optionMapWithInput hb)

/-- Gate lookup takes precedence at actual source vertices; every other pixel retains its original edge identity. -/
def cell (q : Query) : Code :=
  (Raster.vertexAt (q.1.1,q.2)).elim (ordinary q) fun v =>
    some (.inl (v,gateTileState (v,q.1.2)))

private theorem cell_polyTime : ComputableInPolyTime cell encQuery encCode := by
  have hv' := Raster.vertexAt_polyTime
  have hv : ComputableInPolyTime (fun q : Query => Raster.vertexAt (q.1.1,q.2)) encQuery (encOption encVertexData) := by fun_prop
  have hg := gateTileState_polyTime
  have hb : ComputableInPolyTime (fun q : Query × VertexData =>
      some (Sum.inl (β := Wire) (q.2,gateTileState (q.2,q.1.1.2))))
      (encPair encQuery encVertexData) encCode := by fun_prop
  exact hv.optionElimWithInput ordinary_polyTime hb

/-- All cells of the explicit support rectangle, including the actual empty exterior floor. -/
def cells (q : Source) : List (GridRouting.Point × Code) :=
  (List.range (Raster.height q.1)).flatMap fun y =>
    (List.range (Raster.width q.1)).map fun x => ((x,y),cell (q,(x,y)))

theorem cells_polyTime : ComputableInPolyTime cells encSource (encList (encPair Bitmap.encPoint encCode)) := by
  have hw := Raster.width_polyTime
  have hh := Raster.height_polyTime
  have hc := cell_polyTime
  unfold cells
  fun_prop

theorem cell_gate (q : Source) (p : GridRouting.Point) {v : VertexData} (hv : Raster.vertexAt (q.1,p)=some v) :
    cell (q,p)=some (.inl (v,gateTileState (v,q.2))) := by simp only [cell,hv,Option.elim_some]

theorem cell_empty (q : Source) (p : GridRouting.Point)
    (hv : Raster.vertexAt (q.1,p)=none) (he : Raster.owner (q.1,p)=none) : cell (q,p)=none := by
  simp only [cell,hv,Option.elim_none,ordinary,he]

/-- Every ordinary true source-wire pixel produces its actual complete physical instruction and phases. -/
theorem cell_wire (q : Source) (hP : q.1.checkPlane=true) (hT : q.1.WellTyped [] [])
    (p : GridRouting.Point) {e : ℕ} (hv : Raster.vertexAt (q.1,p)=none) (he : Raster.owner (q.1,p)=some e) :
    ∃ k,cell (q,p)=some (.inr (e,(k,!(q.2.1.getD e false),!(q.2.2.getD e false)))) := by
  obtain ⟨k,hk⟩ := Raster.wireAt_defined hP hT he hv
  exact ⟨k,by simp only [cell,hv,Option.elim_none,ordinary,he,Option.elim_some,wireData,hk,Option.map_some]⟩

end PushPuzzle.PushFS.Reduction.CellPlan
