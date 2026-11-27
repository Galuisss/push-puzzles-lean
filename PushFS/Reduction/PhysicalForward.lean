/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.SourceCanonical
public import PushFS.Reduction.PhysicalSourceStep
public import PushFS.Reduction.PhysicalCompiler

/-! Finite source reachability replays to exact whole-board canonical storage states. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL Plan PhysicalBitmap SourceCanonical
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

/-- Every finite legal source path replays on the exact fixed complete physical board. -/
private theorem canonical_reachable (v : CellPlan.Source) (hw : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    {c d : Fin (Word.compile v.1).edgeCount→Bool} (hr : (Word.compile v.1).graph.Reachable c d) :
    Reachable (atlas v hP hT).board (some 1) (canonical v hP hT (configBits c)) (canonical v hP hT (configBits d)) := by
  induction hr with
  | refl=>exact .refl
  | tail _ hs ih=>exact ih.trans (canonical_step v hw hP hT hs)

/-- Recovering the exact serialized source endpoints turns a real canonical trajectory into a solution of the complete storage puzzle. -/
private theorem solvable_of_canonical_reachable (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (ha : v.2.1.length=(Word.compile v.1).edgeCount) (hb : v.2.2.length=(Word.compile v.1).edgeCount)
    (hr : Reachable (atlas v hP hT).board (some 1)
      (canonical v hP hT (configBits ((Word.compile v.1).config v.2.1)))
      (canonical v hP hT (configBits ((Word.compile v.1).config v.2.2)))) :
    (puzzle v hP hT).Solvable (some 1) := by
  refine ⟨canonical v hP hT (configBits ((Word.compile v.1).config v.2.2)),?_,?_⟩
  · rw [canonical_initial_config v hP hT ha] at hr
    exact hr
  · exact (canonical_target_config v hP hT hb).symm

/-- Exact finite source reachability solves the complete actual Push-1FS board. -/
private theorem ncl_reachable_solvable (v : CellPlan.Source) (hw : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (ha : v.2.1.length=(Word.compile v.1).edgeCount) (hb : v.2.2.length=(Word.compile v.1).edgeCount)
    (hr : (Word.compile v.1).graph.Reachable ((Word.compile v.1).config v.2.1) ((Word.compile v.1).config v.2.2)) :
    (puzzle v hP hT).Solvable (some 1) :=
  solvable_of_canonical_reachable v hP hT ha hb (canonical_reachable v hw hP hT hr)

end PushPuzzle.PushFS.Reduction.PhysicalInventory

namespace PushPuzzle.PushFS.Reduction.PhysicalCompiler
open Cslib.Complexity.NCL

/-- Every accepted upstream source instance has a solution on its actual complete checked physical board. -/
theorem checkedCompile_complete {x : PlaneWordAndOrNCL.Instance} (hx : x∈PlaneWordAndOrNCL) :
    (checkedCompile x).Solvable (some 1) := by
  have hc:=checks_of_mem hx
  obtain ⟨_,_,_,_,_,_,hr⟩:=hx
  rw [checkedCompile_eq x hc]
  exact PhysicalInventory.ncl_reachable_solvable (source x) hc.valid hc.plane hc.typed
    hc.initial_width hc.target_width hr

end PushPuzzle.PushFS.Reduction.PhysicalCompiler
