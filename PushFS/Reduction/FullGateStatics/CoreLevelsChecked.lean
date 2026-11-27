/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.CoreLevels

/-! Finite kernel verification of central slot-name preservation for every actual complete gate geometry. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory
set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem coreLevels_checked : ∀k : Geometry,coreLevelsTest (ofGeometry k)=true := by
  rintro ⟨kind,pattern,rotation,incoming⟩
  cases kind <;> fin_cases pattern <;> fin_cases rotation
  all_goals revert incoming; decide +kernel

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
