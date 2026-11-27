/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ControlWires

/-! Location choices select the original directed tunnel; skips retain the same source location. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity

theorem ControlPhase.upper_step {storage : Bool} {I : Instance} {source : State}
    (hreach : SelfClosingDoor.Reachable I.doors I.initial source)
    (j : ℕ) (_hj : j < slots I) (hused : upperUsed I (rank I source.location) j = true)
    {next : Control storage I}
    (hs : Control.Step
      ⟨sourceRegisters I source, .working (upperRow I (rank I source.location) j)⟩ next) :
    next.SourceSafe := by
  by_cases haccept : source.location = I.target
  · exact Or.inl ⟨source, hreach, haccept⟩
  have hlabel := reachable_location_mem I hreach
  have hnot : rank I source.location ≠ rank I I.target := by
    intro he
    exact haccept ((rank_eq_iff I hlabel).mp he)
  have hchoice : j < 2 * I.doors.length ∧
      rank I (channel I j).source = rank I source.location := by
    simpa only [upperUsed, ite_eq_right hnot, decide_eq_true_eq] using hused
  rcases hs.working_cases with hw | hm | hm | hu | hl
  · obtain ⟨index, hrow, rfl⟩ := hw
    have hknown := choice_wire_mem storage I (rank I source.location) j
      (rank_bound I hlabel) hchoice.1 hnot hchoice.2
    have hewire := wires_eq_of_source_eq storage I
      (List.getElem_mem index.isLt) hknown hrow.symm
    let door := channelDoor I ⟨j, hchoice.1⟩
    have hchannel : channel I j = I.doors[door].tunnel (channelBit j) :=
      channel_eq I ⟨j, hchoice.1⟩
    have hentry : source.location = (I.doors[door].tunnel (channelBit j)).source := by
      rw [← hchannel]
      exact (rank_eq_iff I hlabel).mp hchoice.2.symm
    have htarget : (layout storage I).wires[index].target =
        doorBase door.val + (Room.check (channelBit j)).row := by
      calc
        _ = doorBase (j / 2) + (if channelBit j then 50 else 40) :=
          congrArg Wire.target hewire
        _ = _ := by cases hb : channelBit j <;> simp [door, channelDoor, Room.check, Room.Slot.row]
    apply Or.inr
    refine ⟨source, hreach, ?_⟩
    simpa only [sessionRegisters_stable] using
      (ControlPhase.doorWire (storage := storage) door (channelBit j)
        (Room.stable (source.bits.getD door.val false)) (Room.check (channelBit j))
        index 0 hentry Relation.ReflTransGen.refl htarget)
  · obtain ⟨door, value, he, _⟩ := hm
    exact False.elim (upperRow_ne_door_register I _ _ door value he)
  · obtain ⟨door, value, he, _⟩ := hm
    exact False.elim (upperRow_ne_door_register I _ _ door value he)
  · obtain ⟨v, j', p, _, _, hp, he, _⟩ := hu
    have hlaunch : LaunchRow I (upperRow I (rank I source.location) j) :=
      Or.inr ⟨_, _, Or.inl rfl⟩
    rw [he] at hlaunch
    exact False.elim (inputRow_not_launch I v j' p hp hlaunch)
  · obtain ⟨v, j', p, _, _, hp, he, _⟩ := hl
    have hlaunch : LaunchRow I (upperRow I (rank I source.location) j) :=
      Or.inr ⟨_, _, Or.inl rfl⟩
    rw [he] at hlaunch
    exact False.elim (inputRow_not_launch I v j' p hp hlaunch)

theorem ControlPhase.lower_step {storage : Bool} {I : Instance} {source : State}
    (hlabel : source.location ∈ labels I)
    (j : ℕ) (_hj : j < slots I) (hused : lowerUsed I (rank I source.location) j = true)
    {next : Control storage I}
    (hs : Control.Step
      ⟨sourceRegisters I source, .working (lowerRow I (rank I source.location) j)⟩ next) :
    ControlPhase storage I source next := by
  have hchoice : rank I source.location ≠ rank I I.target ∧ j < 2 * I.doors.length := by
    simpa only [lowerUsed, decide_eq_true_eq] using hused
  rcases hs.working_cases with hw | hm | hm | hu | hl
  · obtain ⟨index, hrow, rfl⟩ := hw
    have hknown := skip_wire_mem storage I (rank I source.location) j
      (rank_bound I hlabel) hchoice.2 hchoice.1
    have hewire := wires_eq_of_source_eq storage I
      (List.getElem_mem index.isLt) hknown hrow.symm
    apply ControlPhase.junctionWire index 0 (j + 1) 0
      (by unfold slots; omega) (slots_pos I)
    exact congrArg Wire.target hewire
  · obtain ⟨door, value, he, _⟩ := hm
    exact False.elim (lowerRow_ne_door_register I _ _ door value he)
  · obtain ⟨door, value, he, _⟩ := hm
    exact False.elim (lowerRow_ne_door_register I _ _ door value he)
  · obtain ⟨v, j', p, _, _, hp, he, _⟩ := hu
    have hlaunch : LaunchRow I (lowerRow I (rank I source.location) j) :=
      Or.inr ⟨_, _, Or.inr rfl⟩
    rw [he] at hlaunch
    exact False.elim (inputRow_not_launch I v j' p hp hlaunch)
  · obtain ⟨v, j', p, _, _, hp, he, _⟩ := hl
    have hlaunch : LaunchRow I (lowerRow I (rank I source.location) j) :=
      Or.inr ⟨_, _, Or.inr rfl⟩
    rw [he] at hlaunch
    exact False.elim (inputRow_not_launch I v j' p hp hlaunch)

end PushPuzzle.PushPush.Doors.Source
