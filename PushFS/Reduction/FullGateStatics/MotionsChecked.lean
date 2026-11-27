/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.MotionEnvelopes

/-! The finite physical catalog has disjoint motion intervals across primitive owners. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem motionsApart_checked : ∀k : Geometry,motionsApart (ofGeometry k)=true := by
  rintro ⟨kind,pattern,rotation,incoming⟩
  cases kind <;> fin_cases pattern <;> fin_cases rotation
  all_goals revert incoming; decide +kernel

private theorem motionEnvelopes_geometry (g : GateTileState) (i : Inventory.Index g) :
    motionEnvelopes (ofGeometry (geometry g)) i=motionEnvelopes g i := by
  rcases i with i|(⟨role,j|j⟩|role) <;> rfl

theorem motionsApart_all (g : GateTileState) : motionsApart g=true := by
  have he : motionsApart (ofGeometry (geometry g))=motionsApart g := by
    unfold motionsApart
    rw [funext (motionEnvelopes_geometry g)]
    rfl
  exact he ▸ motionsApart_checked (geometry g)

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
