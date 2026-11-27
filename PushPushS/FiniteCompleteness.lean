/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushS.Completeness
public import PushPushS.FiniteUpperBound

/-! PSPACE-completeness of exact storage with each fixed positive sliding push limit. -/

public section
namespace PushPuzzle.PushPushS

open Cslib.Complexity

/-- The physical compiler solves every source YES instance using only single-box slides. -/
theorem compile_forward_finite (k : ℕ) (hk : 1 ≤ k) (I : SelfClosingDoor.Instance)
    (hs : I ∈ SelfClosingDoor.Reachability) : Instance.SolvableFinite (compile I) k :=
  PushPush.Doors.Source.physical_storage_forward_finite I k hk hs

/-- The same storage compiler is correct at every fixed positive push limit. -/
theorem compile_finite_mem_iff (k : ℕ) (hk : 1 ≤ k) (I : SelfClosingDoor.Instance) :
    I ∈ SelfClosingDoor.Reachability ↔ compile I ∈ solvableFinite k :=
  ⟨compile_forward_finite k hk I, fun hs => compile_sound I hs.unlimited⟩

/-- The explicit door storage compiler gives a standard polynomial-time reduction. -/
theorem polyTimeReducible_reachability_finite (k : ℕ) (hk : 1 ≤ k) :
    PolyTimeReducible SelfClosingDoor.encInstance encoding SelfClosingDoor.Reachability
      (solvableFinite k) :=
  ⟨compile, compile_polyTime, compile_finite_mem_iff k hk⟩

theorem solvable_finite_pspaceHard (k : ℕ) (hk : 1 ≤ k) :
    PSPACEHard encoding (solvableFinite k) :=
  SelfClosingDoor.Reachability_pspaceHard.trans (polyTimeReducible_reachability_finite k hk)

/-- PushPush-kS is PSPACE-complete for every fixed k ≥ 1. -/
theorem solvable_finite_pspaceComplete (k : ℕ) (hk : 1 ≤ k) :
    PSPACEComplete encoding (solvableFinite k) :=
  ⟨solvableFinite_mem_PSPACE k, solvable_finite_pspaceHard k hk⟩

/-- PushPush-1S is PSPACE-complete. -/
theorem solvable_one_pspaceComplete : PSPACEComplete encoding (solvableFinite 1) :=
  solvable_finite_pspaceComplete 1 le_rfl

end PushPuzzle.PushPushS
