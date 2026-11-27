/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalEdgeSignals
public import PushFS.Reduction.PhysicalCoreTags
public import PushFS.Reduction.PhysicalSoundness

/-! Every actual physical successful trajectory recovers original finite NCL reachability, for every push force. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL PushPuzzle.NCL Plan PhysicalBitmap Gadgets.Wires Soundness
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

/-- Every intermediate successful actual physical state has exclusive original-edge inward observations. -/
private theorem sourceReadout_exclusive (v : CellPlan.Source) (hw : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) (hG : (Word.compile v.1).graph.WellFormed)
    {S T : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)}
    (hs : Successful (rawSlotMatching v hP hT) S T) :
    PortClaims.Exclusive ((sourceReadout v hw hP hT hG).read S) := by
  apply sourceReadout_exclusive_of_roles v hw hP hT hG S
  intro g hg r h hh s he htrue hfalse both
  let e : Fin (Word.compile v.1).edgeCount:=⟨(g.ports.port r).edge,vertexRecord_edge_lt v.1 hw hP hT g hg r⟩
  exact port_claims_exclusive v hw hP hT hG e h hh s he.symm hfalse g hg r rfl htrue hs ⟨both.2,both.1⟩

/-- Actual complete-board solvability projects to the exact original finite source graph. -/
private theorem ncl_of_physical_solvable (v : CellPlan.Source) (hw : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (ha : (Word.compile v.1).checkLegal v.2.1=true) (hb : (Word.compile v.1).checkLegal v.2.2=true)
    {cap : Option ℕ} (hsol : (puzzle v hP hT).Solvable cap) :
    (Word.compile v.1).graph.Reachable (fun e=>v.2.1.getD e.val false) (fun e=>v.2.2.getD e.val false) :=
  ncl_of_solvable v hw hP hT (axisTracks v hP hT) (coreTags v hP hT)
    (certificate v hP hT) (matching_ordered v hP hT) ha hb
    (fun _ _ hs=>sourceReadout_exclusive v hw hP hT hw.2.2 hs) hsol
end PushPuzzle.PushFS.Reduction.PhysicalInventory

namespace PushPuzzle.PushFS.Reduction.PhysicalCompiler
open Cslib.Complexity.NCL PushPuzzle.NCL

/-- Any solution of the total checked compiler output certifies membership in the actual upstream source language. -/
theorem checkedCompile_sound {x : PlaneWordAndOrNCL.Instance} {cap : Option ℕ}
    (hs : (checkedCompile x).Solvable cap) : x∈PlaneWordAndOrNCL := by
  apply mem_of_checkedCompile_solvable ?_ hs
  intro x hx hsol
  exact PhysicalInventory.ncl_of_physical_solvable (source x) hx.valid hx.plane hx.typed
    hx.initial_legal hx.target_legal hsol
end PushPuzzle.PushFS.Reduction.PhysicalCompiler
