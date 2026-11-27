/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceMeshAccess

/-! Every literal source-port shoulder is a free, globally accessible point for every normal primitive profile. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Raster.width Raster.height

theorem code_position_bounds (w : ℕ) (v : CellPlan.Source) (pos : GridRouting.Point) (c : PrimitiveCode)
    (hq : (pos,c) ∈ codes w v) : pos.1 < Raster.width v.1 ∧ pos.2 < Raster.height v.1 := by
  have hc := code_local w v (pos,c) hq
  change c ∈ localCodes w (CellPlan.cell (v,pos)) at hc
  apply CellPlan.nonempty_bounds
  intro he
  rw [he] at hc
  simp [localCodes] at hc

private theorem vertical_offset_access (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (phase : Fin (codes w v).length → Bool)
    (x : Fin (Raster.width v.1+1)) (y : Fin (Raster.height v.1)) (face : Direction) (north : Bool)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*x.val+padding w,tileStride w*y.val+padding w+shoulderOffset w face north)) :
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) (PrimitiveProfile.state w hw v phase q) ∧
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase q) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) := by
  by_cases hn : north = lowNorth face
  · simp only [shoulderOffset,hn,↓reduceIte] at hq
    exact vertical_low_shoulder_access w hw v hP hT phase x y q hq
  · simp only [shoulderOffset,hn,↓reduceIte] at hq
    exact vertical_high_shoulder_access w hw v hP hT phase x y q hq

private theorem horizontal_offset_access (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (phase : Fin (codes w v).length → Bool)
    (x : Fin (Raster.width v.1)) (y : Fin (Raster.height v.1+1)) (face : Direction) (north : Bool)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*x.val+padding w+shoulderOffset w face north,tileStride w*y.val+padding w)) :
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) (PrimitiveProfile.state w hw v phase q) ∧
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase q) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) := by
  by_cases hn : north = lowNorth face
  · simp only [shoulderOffset,hn,↓reduceIte] at hq
    exact horizontal_low_shoulder_access w hw v hP hT phase x y q hq
  · simp only [shoulderOffset,hn,↓reduceIte] at hq
    exact horizontal_high_shoulder_access w hw v hP hT phase x y q hq

theorem port_shoulder_access (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (phase : Fin (codes w v).length → Bool)
    (pos : GridRouting.Point) (hb : pos.1 < Raster.width v.1 ∧ pos.2 < Raster.height v.1)
    (face : Direction) (north : Bool) (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos (shoulder w face north)) :
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) (PrimitiveProfile.state w hw v phase q) ∧
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase q) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) := by
  have hh := hq.trans (macro_shoulder w face pos north)
  cases face
  · apply horizontal_offset_access w hw v hP hT phase ⟨pos.1,hb.1⟩ ⟨pos.2,by omega⟩ .north north q
    simpa only [meshFaceBase,reduceCtorEq,false_or,↓reduceIte] using hh
  · apply vertical_offset_access w hw v hP hT phase ⟨pos.1+1,by omega⟩ ⟨pos.2,hb.2⟩ .east north q
    simpa only [meshFaceBase,true_or,↓reduceIte] using hh
  · apply horizontal_offset_access w hw v hP hT phase ⟨pos.1,hb.1⟩ ⟨pos.2+1,by omega⟩ .south north q
    simpa only [meshFaceBase,reduceCtorEq,false_or,↓reduceIte] using hh
  · apply vertical_offset_access w hw v hP hT phase ⟨pos.1,by omega⟩ ⟨pos.2,hb.2⟩ .west north q
    simpa only [meshFaceBase,or_true,↓reduceIte] using hh

theorem port_shoulder_free (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : Fin (codes w v).length → Bool) (pos : GridRouting.Point) (face : Direction) (north : Bool)
    (q : Cell (width w v) (height w v)) (hq : coordinates q = macroShift w pos (shoulder w face north)) :
    Free (inventory w hw v).board (PrimitiveProfile.boxes w hw v phase) q := by
  have hh := hq.trans (macro_shoulder w face pos north)
  have hb := shoulderOffset_free w face north
  cases face
  · apply horizontal_mesh_free_tight w hw v phase pos.1 pos.2 _ hb.1 hb.2 q
    simpa only [meshFaceBase,reduceCtorEq,false_or,↓reduceIte] using hh
  · apply vertical_mesh_free_tight w hw v phase (pos.1+1) pos.2 _ hb.1 hb.2 q
    simpa only [meshFaceBase,true_or,↓reduceIte] using hh
  · apply horizontal_mesh_free_tight w hw v phase pos.1 (pos.2+1) _ hb.1 hb.2 q
    simpa only [meshFaceBase,reduceCtorEq,false_or,↓reduceIte] using hh
  · apply vertical_mesh_free_tight w hw v phase pos.1 pos.2 _ hb.1 hb.2 q
    simpa only [meshFaceBase,or_true,↓reduceIte] using hh

end PushPuzzle.PushS.FiniteSourceInventory
