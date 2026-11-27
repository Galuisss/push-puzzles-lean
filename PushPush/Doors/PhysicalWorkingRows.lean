/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ControlRoute
public import PushPush.Doors.ControlRowParity
public import PushPush.Doors.WireSourcePins

/-! Every working signal lies on a rack-backed input or a literal source or terminal-pin row. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity

def WorkingRowAddress (storage : Bool) (I : Instance) (row : ℕ) : Prop :=
  row ∈ (layout storage I).rackRows ∨
    (∃ i : Fin (layout storage I).wires.length, (layout storage I).wires[i].source = row) ∨
    ∃ i : Fin (layout storage I).wires.length,
      Layout.beside (layout storage I).wires[i].targetSouth (layout storage I).wires[i].target = row

private theorem source_address (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ (layout storage I).wires) : WorkingRowAddress storage I e.source := by
  obtain ⟨i, hi, hwire⟩ := List.mem_iff_getElem.mp he
  exact Or.inr (Or.inl ⟨⟨i, hi⟩, congrArg Wire.source hwire⟩)

private theorem terminal_address (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ (layout storage I).wires) :
    WorkingRowAddress storage I (Layout.beside e.targetSouth e.target) := by
  obtain ⟨i, hi, hwire⟩ := List.mem_iff_getElem.mp he
  exact Or.inr (Or.inr ⟨⟨i, hi⟩, congrArg (fun e => Layout.beside e.targetSouth e.target) hwire⟩)

private theorem check_terminal_address (storage : Bool) (I : Instance) (source : State)
    (hlocation : source.location ∈ labels I) (hnot : source.location ≠ I.target)
    (door : Fin I.doors.length) (bit : Bool)
    (hentry : source.location = (I.doors[door].tunnel bit).source) :
    WorkingRowAddress storage I (doorBase door.val + if bit then 49 else 41) := by
  let j := channelIndex I door bit
  have hsource : rank I (channel I j.val).source = rank I source.location := by
    rw [channel_channelIndex]
    exact congrArg (rank I) hentry.symm
  have hnotRank : rank I source.location ≠ rank I I.target := by
    intro he
    exact hnot ((rank_eq_iff I hlocation).mp he)
  have hm := choice_wire_mem storage I (rank I source.location) j.val
    (rank_bound I hlocation) j.isLt hnotRank hsource
  have haddr := terminal_address storage I hm
  have hdoor := congrArg Fin.val (channelDoor_channelIndex I door bit)
  change j.val / 2 = door.val at hdoor
  have hjbit : channelBit j.val = bit := channelBit_channelIndex I door bit
  rw [hjbit] at haddr
  cases bit <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_false, Bool.not_true,
    Layout.beside] at haddr ⊢
  · simpa only [hdoor, Nat.add_assoc] using haddr
  · have he : doorBase door.val + 50 - 1 = doorBase door.val + 49 := by omega
    simpa only [hdoor, he] using haddr

private theorem landing_address (storage : Bool) (I : Instance) (source : State)
    (hlocation : source.location ∈ labels I) (hnot : source.location ≠ I.target)
    (door : Fin I.doors.length) (channel : Bool) (moving kept : Room.Slot)
    (hentry : source.location = (I.doors[door].tunnel channel).source)
    (ha : kept = .checkA → channel = false) (hb : kept = .checkB → channel = true) :
    WorkingRowAddress storage I (doorBase door.val + Room.landing moving kept) := by
  have h11 := source_address storage I (internal_wire_mem storage I door
    (e := ⟨doorBase door.val + 11, true, doorBase door.val + 30, true⟩) (by simp))
  have h39 := source_address storage I (internal_wire_mem storage I door
    (e := ⟨doorBase door.val + 39, false, doorBase door.val + 80, true⟩) (by simp))
  have h51 := source_address storage I (internal_wire_mem storage I door
    (e := ⟨doorBase door.val + 51, true, doorBase door.val + 10, false⟩) (by simp))
  have h79 := source_address storage I (internal_wire_mem storage I door
    (e := ⟨doorBase door.val + 79, false, doorBase door.val + 60, false⟩) (by simp))
  have h29 := source_address storage I (arrival_wire_mem storage I
    (channelIndex I door true).val (channelIndex I door true).isLt)
  rw [arrival_channelIndex_source] at h29
  have h61 := source_address storage I (arrival_wire_mem storage I
    (channelIndex I door false).val (channelIndex I door false).isLt)
  rw [arrival_channelIndex_source] at h61
  have h9 := terminal_address storage I (internal_wire_mem storage I door
    (e := ⟨doorBase door.val + 51, true, doorBase door.val + 10, false⟩) (by simp))
  have h31 := terminal_address storage I (internal_wire_mem storage I door
    (e := ⟨doorBase door.val + 11, true, doorBase door.val + 30, true⟩) (by simp))
  have h59 := terminal_address storage I (internal_wire_mem storage I door
    (e := ⟨doorBase door.val + 79, false, doorBase door.val + 60, false⟩) (by simp))
  have h81 := terminal_address storage I (internal_wire_mem storage I door
    (e := ⟨doorBase door.val + 39, false, doorBase door.val + 80, true⟩) (by simp))
  simp only [Bool.false_eq_true, ite_false, ite_true, Layout.beside] at h9 h31 h59 h81 h29 h61
  have he9 : doorBase door.val + 10 - 1 = doorBase door.val + 9 := by omega
  have he59 : doorBase door.val + 60 - 1 = doorBase door.val + 59 := by omega
  simp only [he9, he59, Nat.add_assoc] at h9 h31 h59 h81
  cases kept
  · by_cases hl : moving.row < 10
    ·
      change WorkingRowAddress storage I (doorBase door.val + (if moving.row < 10 then 9 else 11))
      rw [ite_eq_left hl]
      exact h9
    ·
      change WorkingRowAddress storage I (doorBase door.val + (if moving.row < 10 then 9 else 11))
      rw [ite_eq_right hl]
      exact h11
  · by_cases hl : moving.row < 30
    ·
      change WorkingRowAddress storage I (doorBase door.val + (if moving.row < 30 then 29 else 31))
      rw [ite_eq_left hl]
      exact h29
    ·
      change WorkingRowAddress storage I (doorBase door.val + (if moving.row < 30 then 29 else 31))
      rw [ite_eq_right hl]
      exact h31
  · by_cases hl : moving.row < 40
    ·
      change WorkingRowAddress storage I (doorBase door.val + (if moving.row < 40 then 39 else 41))
      rw [ite_eq_left hl]
      exact h39
    ·
      have h41 := check_terminal_address storage I source hlocation hnot door false (by simpa only [ha rfl] using hentry)
      change WorkingRowAddress storage I (doorBase door.val + (if moving.row < 40 then 39 else 41))
      rw [ite_eq_right hl]
      exact h41
  · by_cases hl : moving.row < 50
    ·
      have h49 := check_terminal_address storage I source hlocation hnot door true (by simpa only [hb rfl] using hentry)
      change WorkingRowAddress storage I (doorBase door.val + (if moving.row < 50 then 49 else 51))
      rw [ite_eq_left hl]
      exact h49
    ·
      change WorkingRowAddress storage I (doorBase door.val + (if moving.row < 50 then 49 else 51))
      rw [ite_eq_right hl]
      exact h51
  · by_cases hl : moving.row < 60
    ·
      change WorkingRowAddress storage I (doorBase door.val + (if moving.row < 60 then 59 else 61))
      rw [ite_eq_left hl]
      exact h59
    ·
      change WorkingRowAddress storage I (doorBase door.val + (if moving.row < 60 then 59 else 61))
      rw [ite_eq_right hl]
      exact h61
  · by_cases hl : moving.row < 80
    ·
      change WorkingRowAddress storage I (doorBase door.val + (if moving.row < 80 then 79 else 81))
      rw [ite_eq_left hl]
      exact h79
    ·
      change WorkingRowAddress storage I (doorBase door.val + (if moving.row < 80 then 79 else 81))
      rw [ite_eq_right hl]
      exact h81

theorem ControlPhase.working_row_address {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C)
    (hreach : SelfClosingDoor.Reachable I.doors I.initial source)
    (row : ℕ) (hworking : C.signal = .working row) :
    I ∈ SelfClosingDoor.Reachability ∨ WorkingRowAddress storage I row := by
  by_cases haccept : source.location = I.target
  · exact Or.inl ⟨source, hreach, haccept⟩
  have hlocation := reachable_location_mem I hreach
  apply Or.inr
  cases hphase with
  | junction j p hj hp =>
    cases hworking
    exact Or.inl (junction_input_rack_mem storage I (rank_bound I hlocation) hj hp)
  | upper j hj hused =>
    cases hworking
    have hnot : rank I source.location ≠ rank I I.target := by
      intro he; exact haccept ((rank_eq_iff I hlocation).mp he)
    have hc : j < 2 * I.doors.length ∧ rank I (channel I j).source = rank I source.location := by
      simpa only [upperUsed, ite_eq_right hnot, decide_eq_true_eq] using hused
    exact source_address storage I (choice_wire_mem storage I _ j (rank_bound I hlocation) hc.1 hnot hc.2)
  | lower j hj hused =>
    cases hworking
    have hc : rank I source.location ≠ rank I I.target ∧ j < 2 * I.doors.length := by
      simpa only [lowerUsed, decide_eq_true_eq] using hused
    exact source_address storage I (skip_wire_mem storage I _ j (rank_bound I hlocation) hc.2 hc.1)
  | call door channel stored incoming hentry hsession =>
    cases hworking
    exact Or.inl (door_slot_rack_mem storage I door.isLt (by cases incoming <;> simp [Room.Slot.row]))
  | result door channel stored incoming keep hentry hsession =>
    cases hworking
    cases keep
    · apply landing_address storage I source hlocation haccept door channel incoming stored hentry
      · exact fun h => Room.reachable_call_checkA_channel _ _ _ _ hsession (Or.inl h)
      · exact fun h => Room.reachable_call_checkB_channel _ _ _ _ hsession (Or.inl h)
    · apply landing_address storage I source hlocation haccept door channel stored incoming hentry
      · exact fun h => Room.reachable_call_checkA_channel _ _ _ _ hsession (Or.inr h)
      · exact fun h => Room.reachable_call_checkB_channel _ _ _ _ hsession (Or.inr h)
  | junctionWire index corner j p hj hp htarget => cases hworking
  | doorWire door channel stored incoming index corner hentry hsession htarget => cases hworking

theorem ControlPhase.working_row_fit {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C)
    (hlocation : source.location ∈ labels I) (row : ℕ) (hworking : C.signal = .working row) :
    row ≤ (layout storage I).depth := by
  cases hphase with
  | junction j p hj hp =>
    cases hworking
    exact inputRow_fit storage I (rank_bound I hlocation) hj hp
  | upper j hj hused =>
    cases hworking
    exact upperRow_fit storage I (rank_bound I hlocation) hj
  | lower j hj hused =>
    cases hworking
    exact lowerRow_fit storage I (rank_bound I hlocation) hj
  | call door channel stored incoming hentry hsession =>
    cases hworking
    exact doorRow_fit storage I door.isLt (by have := Room.slot_row_bounds incoming; omega)
  | result door channel stored incoming keep hentry hsession =>
    cases hworking
    cases keep
    · simpa only [Bool.false_eq_true, ite_false] using
        (doorRow_fit storage I (offset := Room.landing incoming stored) door.isLt
          (by have := landing_bounds incoming stored; omega))
    · simpa only [ite_true] using
        (doorRow_fit storage I (offset := Room.landing stored incoming) door.isLt
          (by have := landing_bounds stored incoming; omega))
  | junctionWire index corner j p hj hp htarget => cases hworking
  | doorWire door channel stored incoming index corner hentry hsession htarget => cases hworking

end PushPuzzle.PushPush.Doors.Source
