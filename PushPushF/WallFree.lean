/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushF.Encoding
public import PushPush.Basic

/-! Empty-wall boards preserve the wall-free player destination problem. -/

@[expose] public section
namespace PushPuzzle.PushPushF

/-- View a wall-free player destination instance as a board with fixed walls. -/
def ofWallFree (I : PushPush.Instance) : Instance where
  width := I.width
  height := I.height
  walls := ∅
  initial := I.initial
  target := I.target
  initial_valid := I.initial_valid
  target_floor := Finset.notMem_empty _

/-- The embedding preserves every maximum-slide solution. -/
theorem solvable_wallFree_iff (I : PushPush.Instance) :
    Instance.Solvable (ofWallFree I) ↔ PushPush.Instance.Solvable I := by
  constructor <;> rintro ⟨t, hr, hg⟩
  · exact ⟨t, (PushPushFS.Unlimited.reachable_wallFree_iff (by rfl)).mp hr, hg⟩
  · exact ⟨t, (PushPushFS.Unlimited.reachable_wallFree_iff (by rfl)).mpr hr, hg⟩

end PushPuzzle.PushPushF
