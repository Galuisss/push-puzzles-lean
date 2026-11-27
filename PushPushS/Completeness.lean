/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushS.Forward
public import PushPushS.UpperBound
public import PushPush.Doors.StorageSoundness
public import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.Completeness

/-! Standard PSPACE-completeness of wall-free unlimited maximum sliding with exact storage. -/

public section
namespace PushPuzzle.PushPushS

open Cslib.Complexity

theorem compile_sound (I : SelfClosingDoor.Instance) (hs : Instance.Solvable (compile I)) :
    I ∈ SelfClosingDoor.Reachability := by
  obtain ⟨final, hactual, hgoals⟩ := hs
  exact PushPush.Doors.Source.physical_storage_sound I hactual hgoals

theorem compile_mem_iff (I : SelfClosingDoor.Instance) :
    I ∈ SelfClosingDoor.Reachability ↔ compile I ∈ solvable :=
  ⟨compile_forward I, compile_sound I⟩

theorem polyTimeReducible_reachability :
    PolyTimeReducible SelfClosingDoor.encInstance encoding SelfClosingDoor.Reachability solvable :=
  ⟨compile, compile_polyTime, compile_mem_iff⟩

theorem solvable_pspaceHard : PSPACEHard encoding solvable :=
  SelfClosingDoor.Reachability_pspaceHard.trans polyTimeReducible_reachability

theorem solvable_pspaceComplete : PSPACEComplete encoding solvable :=
  ⟨solvable_mem_PSPACE, solvable_pspaceHard⟩

end PushPuzzle.PushPushS
