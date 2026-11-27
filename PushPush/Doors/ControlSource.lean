/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ControlRoute

/-! Every safe control execution retains one genuine original source path. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity

private theorem result_step_core {storage : Bool} {I : Instance} {source : State}
    (hreach : SelfClosingDoor.Reachable I.doors I.initial source)
    (door : Fin I.doors.length) (channel : Bool) (stored incoming moving kept : Room.Slot)
    (hentry : source.location = (I.doors[door].tunnel channel).source)
    (hsession : Room.Reachable
      (.call (Room.stable (source.bits.getD door.val false)) (Room.check channel))
      (.call stored incoming))
    (hadvance : ∀ node, Room.route kept (Room.landing moving kept) = some node →
      Room.Step (.call stored incoming) node)
    {next : Control storage I}
    (hs : Control.Step
      ⟨sessionRegisters I source door kept, .working (doorBase door.val + Room.landing moving kept)⟩ next) :
    next.SourceSafe := by
  rcases hs.working_cases with hw | hm | hm | hu | hl
  · obtain ⟨index, hrow, rfl⟩ := hw
    obtain ⟨node, hroute⟩ := route_some_of_wire storage I door moving kept index hrow.symm
    have hrun := hsession.tail (hadvance node hroute)
    have htarget := route_wire_target storage I door kept (Room.landing moving kept)
      node index hrow.symm hroute
    cases node with
    | call newStored newIncoming =>
      obtain ⟨hkept, htarget⟩ := htarget
      subst newStored
      exact Or.inr ⟨source, hreach,
        .doorWire door channel kept newIncoming index 0 hentry hrun htarget⟩
    | exit out newStored =>
      obtain ⟨hkept, htarget⟩ := htarget
      subst newStored
      have hvalid := SelfClosingDoor.Reachable.valid hreach I.initial_valid
      obtain ⟨nextSource, hstep, hlocation, hregister⟩ :=
        room_exit_source_step I source hvalid door channel out kept hentry hrun
      have hout := ((Room.reachable_exit_iff (source.bits.getD door.val false)
        channel out kept).mp hrun).2.1
      have htarget' : (layout storage I).wires[index].target =
          inputRow I (rank I nextSource.location) 0 (channelIndex I door channel).val := by
        simpa only [hlocation, hout] using htarget
      apply Or.inr
      refine ⟨nextSource, hreach.tail hstep, ?_⟩
      rw [hregister]
      exact .junctionWire index 0 0 (channelIndex I door channel).val (slots_pos I)
        (by have := (channelIndex I door channel).isLt; unfold slots; omega) htarget'
  · obtain ⟨other, value, he, _⟩ := hm
    exact False.elim (result_ne_door_register I door other moving kept value he)
  · obtain ⟨other, value, he, _⟩ := hm
    exact False.elim (result_ne_door_register I door other moving kept value he)
  · obtain ⟨v, j, p, _, _, _, he, _⟩ := hu
    exact False.elim (result_ne_inputRow I door moving kept v j p he)
  · obtain ⟨v, j, p, _, _, _, he, _⟩ := hl
    exact False.elim (result_ne_inputRow I door moving kept v j p he)

private theorem ControlPhase.result_step {storage : Bool} {I : Instance} {source : State}
    (hreach : SelfClosingDoor.Reachable I.doors I.initial source)
    (door : Fin I.doors.length) (channel : Bool) (stored incoming : Room.Slot)
    (keep : Bool) (hentry : source.location = (I.doors[door].tunnel channel).source)
    (hsession : Room.Reachable
      (.call (Room.stable (source.bits.getD door.val false)) (Room.check channel))
      (.call stored incoming)) {next : Control storage I}
    (hs : Control.Step
      ⟨sessionRegisters I source door (if keep then incoming else stored),
        .working (doorBase door.val + if keep then Room.landing stored incoming
          else Room.landing incoming stored)⟩ next) : next.SourceSafe := by
  have hdistinct := Room.reachable_call_distinct (source.bits.getD door.val false)
    channel stored incoming hsession
  cases keep
  · exact result_step_core hreach door channel stored incoming incoming stored hentry hsession
      (fun node hroute => ⟨hdistinct, false, hroute⟩) hs
  · exact result_step_core hreach door channel stored incoming stored incoming hentry hsession
      (fun node hroute => ⟨hdistinct, true, hroute⟩) hs

/-- One safe chamber or wire action preserves an actual original source execution. -/
private theorem Control.SourceSafe.step {storage : Bool} {I : Instance}
    {current next : Control storage I} (hcurrent : current.SourceSafe)
    (hs : Control.Step current next) : next.SourceSafe := by
  rcases hcurrent with haccept | ⟨source, hreach, hphase⟩
  · exact Or.inl haccept
  · cases hphase with
    | junction j p hj hp =>
      exact Or.inr ⟨source, hreach, ControlPhase.junction_step j p hj hp hs⟩
    | upper j hj hused => exact ControlPhase.upper_step hreach j hj hused hs
    | lower j hj hused =>
      exact Or.inr ⟨source, hreach,
        ControlPhase.lower_step (reachable_location_mem I hreach) j hj hused hs⟩
    | junctionWire index corner j p hj hp htarget =>
      exact Or.inr ⟨source, hreach,
        ControlPhase.junctionWire_step index corner j p hj hp htarget hs⟩
    | call door channel stored incoming hentry hsession =>
      exact Or.inr ⟨source, hreach,
        ControlPhase.call_step door channel stored incoming hentry hsession hs⟩
    | result door channel stored incoming keep hentry hsession =>
      exact ControlPhase.result_step hreach door channel stored incoming keep hentry hsession hs
    | doorWire door channel stored incoming index corner hentry hsession htarget =>
      exact Or.inr ⟨source, hreach,
        ControlPhase.doorWire_step door channel stored incoming index corner hentry hsession htarget hs⟩

/-- The explicit source compiler's safe control machine always carries a genuine source path. -/
theorem Control.Reachable.sourceSafe {storage : Bool} {I : Instance} {next : Control storage I}
    (hr : Control.Reachable (Control.initial storage I) next) : next.SourceSafe := by
  induction hr with
  | refl => exact Control.initial_sourceSafe storage I
  | tail _ hs ih => exact ih.step hs

end PushPuzzle.PushPush.Doors.Source
