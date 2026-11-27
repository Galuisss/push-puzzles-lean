/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalMarkPhases
public import PushFS.Reduction.StorageProfiles
public import PushFS.WallCongruence

/-! Both endpoints of an actual mixed-phase replay are the complete canonical states on the original board. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory


open Cslib.Complexity.NCL PhysicalBitmap
set_option maxRecDepth 65536
attribute [local irreducible] Raster.width Raster.height

private theorem initial_retarget (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (a b : List Bool) :
    (atlas (v.1,(a,b)) hP hT).initial=canonical v hP hT a := by
  apply State.ext
  · rfl
  · exact marks_eq false (v.1,(a,b)) hP hT a v.2.2 rfl

theorem target_canonical (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (a b : List Bool) :
    (atlas (v.1,(a,b)) hP hT).board.goals=(canonical v hP hT b).boxes := by
  have hf:=canonical_final_boxes (v.1,(a,b)) hP hT
  exact hf.symm.trans (congrArg State.boxes (initial_retarget v hP hT b b))

private theorem profile_initial_canonical (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (a b : List Bool) :
    (atlas (v.1,(a,b)) hP hT).profileAt (fun _=>false) (atlas v hP hT).player=
      canonical v hP hT a := by
  apply State.ext
  · rfl
  · rw [StorageAtlas.profileAt,StorageAtlas.profile_initial]
    exact congrArg State.boxes (initial_retarget v hP hT a b)

private theorem profile_target_canonical (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (a b : List Bool) :
    (atlas (v.1,(a,b)) hP hT).profileAt (fun _=>true) (atlas v hP hT).player=
      canonical v hP hT b := by
  apply State.ext
  · rfl
  · rw [StorageAtlas.profileAt,StorageAtlas.profile_target]
    exact target_canonical v hP hT a b

/-- A complete actual mixed-phase replay gives the canonical transition on the original fixed board. -/
theorem canonical_of_profile_replay (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (a b : List Bool)
    (hr : Reachable (atlas (v.1,(a,b)) hP hT).board (some 1)
      ((atlas (v.1,(a,b)) hP hT).profileAt (fun _=>false) (atlas v hP hT).player)
      ((atlas (v.1,(a,b)) hP hT).profileAt (fun _=>true) (atlas v hP hT).player)) :
    Reachable (atlas v hP hT).board (some 1) (canonical v hP hT a) (canonical v hP hT b) := by
  rw [profile_initial_canonical,profile_target_canonical] at hr
  exact hr.reboard (walls_eq v hP hT a b).symm

end PushPuzzle.PushFS.Reduction.PhysicalInventory
