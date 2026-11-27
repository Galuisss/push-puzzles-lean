/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Shape

/-! Kernel verification of every actual active chart endpoint in all 144 physical gate geometries. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem coverage_checked : ∀k : Geometry,coverageTest (ofGeometry k)=true := by
  rintro ⟨kind,pattern,rotation,incoming⟩
  cases kind <;> fin_cases pattern <;> fin_cases rotation
  all_goals
    rcases incoming with ⟨left, upper, right⟩
    cases left <;> cases upper <;> cases right <;> decide +kernel

theorem coverage_all (g : GateTileState) : coverageTest g=true := by
  rw [←coverage_geometry g]
  exact coverage_checked (geometry g)

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
