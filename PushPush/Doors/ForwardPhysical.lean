/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ForwardCleanup
public import PushPush.Doors.WireSourceForward

/-! Complete physical door-network simulation on the emitted finite work board. -/

public section
namespace PushPuzzle.PushPush.Doors.Source

/-- Every private wire executes by single-box slides with its actual pins and player paths. -/
private theorem wireSimulation (storage : Bool) (I : Instance) : WireSimulation storage I :=
  fun S e he hsignal hregister => S.forward_wire storage e he hsignal hregister

/-- Every YES network reaches the actual target room with the corresponding stable registers. -/
private theorem physical_reaches_target_single (storage : Bool) (I : Instance)
    (hs : I ∈ Cslib.Complexity.SelfClosingDoor.Reachability) :
    ∃ (s : State) (port : ℕ), s.location = I.target ∧ port < slots I ∧
      Finite.Reachable 1 (puzzle storage I).initial ((encodedState storage I s port).canonical storage) :=
  encodedState_reaches_target storage I (wireSimulation storage I) hs

/-- Single-box slides reach the complete state-independent storage goal. -/
theorem physical_storage_forward_single (I : Instance)
    (hs : I ∈ Cslib.Complexity.SelfClosingDoor.Reachability) :
    ∃ t, Finite.Reachable 1 (puzzle true I).initial t ∧ t.boxes = (puzzle true I).board.goals :=
  puzzle_forward I (wireSimulation true I) hs

/-- Every YES network reaches its physical target room. -/
theorem physical_reaches_target (storage : Bool) (I : Instance)
    (hs : I ∈ Cslib.Complexity.SelfClosingDoor.Reachability) :
    ∃ (s : State) (port : ℕ), s.location = I.target ∧ port < slots I ∧
      Reachable (puzzle storage I).initial ((encodedState storage I s port).canonical storage) := by
  obtain ⟨s, port, ht, hp, hr⟩ := physical_reaches_target_single storage I hs
  exact ⟨s, port, ht, hp, hr.unlimited⟩

/-- Every YES network has its complete exact-storage solution. -/
theorem physical_storage_forward (I : Instance)
    (hs : I ∈ Cslib.Complexity.SelfClosingDoor.Reachability) :
    ∃ t, Reachable (puzzle true I).initial t ∧ t.boxes = (puzzle true I).board.goals := by
  obtain ⟨t, hr, ht⟩ := physical_storage_forward_single I hs
  exact ⟨t, hr.unlimited, ht⟩

/-- Every fixed positive push limit admits the canonical single-box storage solution. -/
theorem physical_storage_forward_finite (I : Instance) (k : ℕ) (hk : 1 ≤ k)
    (hs : I ∈ Cslib.Complexity.SelfClosingDoor.Reachability) :
    ∃ t, Finite.Reachable k (puzzle true I).initial t ∧ t.boxes = (puzzle true I).board.goals := by
  obtain ⟨t, hr, ht⟩ := physical_storage_forward_single I hs
  exact ⟨t, hr.mono hk, ht⟩

end PushPuzzle.PushPush.Doors.Source
