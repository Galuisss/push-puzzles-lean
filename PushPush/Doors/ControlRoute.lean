/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ControlLocation

/-! Every live door output follows its original internal or arrival wire. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

private theorem landing_ne_erase_launch (moving stationary : Room.Slot) :
    Room.landing moving stationary ≠ 69 := by
  have ha := Room.landing_adjacent moving stationary
  cases stationary <;> simp only [Room.Slot.row] at ha <;> omega

theorem route_some_of_wire (storage : Bool) (I : Instance) (door : Fin I.doors.length)
    (moving kept : Room.Slot) (index : Fin (layout storage I).wires.length)
    (hsource : (layout storage I).wires[index].source =
      doorBase door.val + Room.landing moving kept) :
    ∃ node, Room.route kept (Room.landing moving kept) = some node := by
  have hl : LaunchRow I (layout storage I).wires[index].source :=
    wires_launch storage I (List.getElem_mem index.isLt)
  rw [hsource] at hl
  have hb := landing_bounds moving kept
  have hd := door_row_before I door.isLt (by omega : Room.landing moving kept < 90)
  have hoff : DoorLaunchOffset (Room.landing moving kept) := by
    rcases hl with ⟨i, hi, offset, ho, he⟩ | ⟨v, j, he | he⟩
    · have ho' : offset < 90 := by simp only [DoorLaunchOffset] at ho; omega
      have hu := row_address_injective (by omega : Room.landing moving kept < 90) ho'
        (show 90 * door.val + Room.landing moving kept = 90 * i + offset by
          simpa only [doorBase] using he)
      exact hu.2 ▸ ho
    · unfold upperRow roomBase at he
      omega
    · have hh := chamberHeight_ge I
      unfold lowerRow roomBase at he
      omega
  have h69 := landing_ne_erase_launch moving kept
  simp only [DoorLaunchOffset] at hoff
  rcases hoff with h | h | h | h | h | h | h <;>
    simp_all [Room.route]

/-- Read the next control input from a routed room output. -/
def RouteTarget (I : Instance) (door : Fin I.doors.length) (kept : Room.Slot)
    (wire : Wire) : Room.Node → Prop
  | .call stored incoming => stored = kept ∧ wire.target = doorBase door.val + incoming.row
  | .exit bit stored => stored = kept ∧ wire.target =
      inputRow I (rank I (I.doors[door].tunnel bit).target) 0 (channelIndex I door bit).val

/-- The named route uses the exact wire emitted by the same original door. -/
theorem route_wire_target (storage : Bool) (I : Instance) (door : Fin I.doors.length)
    (kept : Room.Slot) (row : ℕ) (node : Room.Node)
    (index : Fin (layout storage I).wires.length)
    (hsource : (layout storage I).wires[index].source = doorBase door.val + row)
    (hroute : Room.route kept row = some node) :
    RouteTarget I door kept (layout storage I).wires[index] node := by
  unfold Room.route at hroute
  split_ifs at hroute with h11 h29 h39 h51 h61 h79
  · subst row
    cases hroute
    have hm := internal_wire_mem storage I door (e := ⟨doorBase door.val + 11, true,
      doorBase door.val + 30, true⟩) (by simp)
    have hw := wires_eq_of_source_eq storage I (List.getElem_mem index.isLt) hm hsource
    exact ⟨rfl, congrArg Wire.target hw⟩
  · subst row
    cases hroute
    have hm := arrival_wire_mem storage I (channelIndex I door true).val (channelIndex I door true).isLt
    have hsrc := arrival_channelIndex_source I door true
    have hw := wires_eq_of_source_eq storage I (List.getElem_mem index.isLt) hm
      (hsource.trans hsrc.symm)
    exact ⟨rfl, (congrArg Wire.target hw).trans (arrival_channelIndex_target I door true)⟩
  · subst row
    cases hroute
    have hm := internal_wire_mem storage I door (e := ⟨doorBase door.val + 39, false,
      doorBase door.val + 80, true⟩) (by simp)
    have hw := wires_eq_of_source_eq storage I (List.getElem_mem index.isLt) hm hsource
    exact ⟨rfl, congrArg Wire.target hw⟩
  · subst row
    cases hroute
    have hm := internal_wire_mem storage I door (e := ⟨doorBase door.val + 51, true,
      doorBase door.val + 10, false⟩) (by simp)
    have hw := wires_eq_of_source_eq storage I (List.getElem_mem index.isLt) hm hsource
    exact ⟨rfl, congrArg Wire.target hw⟩
  · subst row
    cases hroute
    have hm := arrival_wire_mem storage I (channelIndex I door false).val (channelIndex I door false).isLt
    have hsrc := arrival_channelIndex_source I door false
    have hw := wires_eq_of_source_eq storage I (List.getElem_mem index.isLt) hm
      (hsource.trans hsrc.symm)
    exact ⟨rfl, (congrArg Wire.target hw).trans (arrival_channelIndex_target I door false)⟩
  · subst row
    cases hroute
    have hm := internal_wire_mem storage I door (e := ⟨doorBase door.val + 79, false,
      doorBase door.val + 60, false⟩) (by simp)
    have hw := wires_eq_of_source_eq storage I (List.getElem_mem index.isLt) hm hsource
    exact ⟨rfl, congrArg Wire.target hw⟩
end PushPuzzle.PushPush.Doors.Source
