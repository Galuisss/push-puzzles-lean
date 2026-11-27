/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.CompilerBounds

/-! Source launch rows and terminal-pin rows occupy disjoint chamber addresses. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors.Source

/-- Recover a chamber number and an offset from a uniform row address. -/
theorem row_address_injective {stride a b u v : ℕ} (hu : u < stride) (hv : v < stride)
    (he : stride * a + u = stride * b + v) : a = b ∧ u = v := by
  have hab : a = b := by
    by_contra h
    rcases Nat.lt_or_gt_of_ne h with h | h
    · have hm : stride * a + stride ≤ stride * b := by
        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left stride (Nat.succ_le_of_lt h)
      omega
    · have hm : stride * b + stride ≤ stride * a := by
        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left stride (Nat.succ_le_of_lt h)
      omega
  exact ⟨hab, by subst b; omega⟩

/-- Rows on which a signal can be emitted from a door chamber. -/
def DoorLaunchOffset (offset : ℕ) : Prop :=
  offset = 11 ∨ offset = 29 ∨ offset = 39 ∨ offset = 51 ∨
    offset = 61 ∨ offset = 69 ∨ offset = 79

/-- The invalid-output side of every wired door input. -/
def DoorPinOffset (offset : ℕ) : Prop :=
  offset = 9 ∨ offset = 31 ∨ offset = 41 ∨ offset = 49 ∨
    offset = 59 ∨ offset = 71 ∨ offset = 81

/-- All possible launch rows in the regular source layout. -/
def LaunchRow (I : Instance) (row : ℕ) : Prop :=
  (∃ i < I.doors.length, ∃ offset, DoorLaunchOffset offset ∧ row = doorBase i + offset) ∨
    ∃ v j, row = upperRow I v j ∨ row = lowerRow I v j

/-- All possible final-pin rows in the regular source layout. -/
def TerminalPinRow (I : Instance) (row : ℕ) : Prop :=
  (∃ i < I.doors.length, ∃ offset, DoorPinOffset offset ∧ row = doorBase i + offset) ∨
    ∃ v j p, p < slots I ∧ row = inputRow I v j p + 1

private theorem launch_terminal_disjoint (I : Instance) {row : ℕ}
    (hl : LaunchRow I row) (ht : TerminalPinRow I row) : False := by
  have hh := chamberHeight_ge I
  rcases hl with ⟨i, hi, a, ha, rfl⟩ | ⟨v, j, he | he⟩
  · have ha' : a < 90 := by simp only [DoorLaunchOffset] at ha; omega
    have hib := door_row_before I hi ha'
    rcases ht with ⟨k, hk, b, hb, he⟩ | ⟨v, j, p, hp, he⟩
    · have hb' : b < 90 := by simp only [DoorPinOffset] at hb; omega
      have hu := row_address_injective ha' hb' (by simpa only [doorBase] using he)
      simp only [DoorLaunchOffset] at ha
      simp only [DoorPinOffset] at hb
      omega
    · unfold inputRow roomBase at he
      omega
  · subst row
    rcases ht with ⟨i, hi, a, ha, he⟩ | ⟨v', j', p, hp, he⟩
    · have ha' : a < 90 := by simp only [DoorPinOffset] at ha; omega
      have hib := door_row_before I hi ha'
      unfold upperRow roomBase at he
      omega
    · have hbound : 11 + 8 * p < chamberHeight I := by unfold chamberHeight; omega
      have he' : chamberHeight I * (slots I * v + j) + 3 =
          chamberHeight I * (slots I * v' + j') + (11 + 8 * p) := by
        unfold upperRow inputRow roomBase at he
        omega
      have hu := row_address_injective (by omega : 3 < chamberHeight I) hbound he'
      omega
  · subst row
    rcases ht with ⟨i, hi, a, ha, he⟩ | ⟨v', j', p, hp, he⟩
    · have ha' : a < 90 := by simp only [DoorPinOffset] at ha; omega
      have hib := door_row_before I hi ha'
      unfold lowerRow roomBase at he
      omega
    · have hbound : 11 + 8 * p < chamberHeight I := by unfold chamberHeight; omega
      have he' : chamberHeight I * (slots I * v + j) + (chamberHeight I - 3) =
          chamberHeight I * (slots I * v' + j') + (11 + 8 * p) := by
        unfold lowerRow inputRow roomBase at he
        omega
      have hu := row_address_injective (by omega : chamberHeight I - 3 < chamberHeight I)
        hbound he'
      unfold chamberHeight at hu
      omega

private theorem internalWires_launch (I : Instance) {e : Wire} (he : e ∈ internalWires I) :
    LaunchRow I e.source := by
  obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
  have hi := List.mem_range.mp hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    exact Or.inl ⟨i, hi, _, by simp [DoorLaunchOffset], rfl⟩

private theorem arrivalWires_launch (I : Instance) {e : Wire} (he : e ∈ arrivalWires I) :
    LaunchRow I e.source := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
  have hj := List.mem_range.mp hj
  apply Or.inl
  refine ⟨j / 2, by omega, _, ?_, rfl⟩
  unfold DoorLaunchOffset
  cases channelBit j <;> simp

private theorem choiceWires_launch (I : Instance) {e : Wire} (he : e ∈ choiceWires I) :
    LaunchRow I e.source := by
  obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
  obtain ⟨j, _, he⟩ := List.mem_flatMap.mp he
  simp only [List.mem_ite_nil_right, List.mem_singleton] at he
  obtain ⟨_, rfl⟩ := he
  exact Or.inr ⟨v, j, Or.inl rfl⟩

private theorem skipWires_launch (I : Instance) {e : Wire} (he : e ∈ skipWires I) :
    LaunchRow I e.source := by
  obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
  obtain ⟨j, _, he⟩ := List.mem_flatMap.mp he
  simp only [List.mem_ite_nil_right, List.mem_singleton] at he
  obtain ⟨_, rfl⟩ := he
  exact Or.inr ⟨v, j, Or.inr rfl⟩

private theorem cleanupWires_launch (I : Instance) {e : Wire} (he : e ∈ cleanupWires I) :
    LaunchRow I e.source := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
  have hi := List.mem_range.mp hi
  by_cases hz : i = 0
  · simp only [ite_eq_left hz]
    exact Or.inr ⟨rank I I.target, 0, Or.inl rfl⟩
  · simp only [ite_eq_right hz]
    exact Or.inl ⟨i - 1, by omega, 69, by simp [DoorLaunchOffset], rfl⟩

theorem wires_launch (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ (layout storage I).wires) : LaunchRow I e.source := by
  simp only [layout, wires, List.mem_append] at he
  rcases he with (((he | he) | he) | he) | he
  · exact internalWires_launch I he
  · exact arrivalWires_launch I he
  · exact choiceWires_launch I he
  · exact skipWires_launch I he
  · cases storage
    · simp at he
    · exact cleanupWires_launch I he

private theorem internalWires_terminalPin (I : Instance) {e : Wire} (he : e ∈ internalWires I) :
    TerminalPinRow I (Layout.beside e.targetSouth e.target) := by
  obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
  have hi := List.mem_range.mp hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨i, hi, 81, by simp [DoorPinOffset], by simp [Layout.beside]⟩
  · exact Or.inl ⟨i, hi, 59, by simp [DoorPinOffset], by simp [Layout.beside]⟩
  · exact Or.inl ⟨i, hi, 9, by simp [DoorPinOffset], by simp [Layout.beside]⟩
  · exact Or.inl ⟨i, hi, 31, by simp [DoorPinOffset], by simp [Layout.beside]⟩

private theorem arrivalWires_terminalPin (I : Instance) {e : Wire} (he : e ∈ arrivalWires I) :
    TerminalPinRow I (Layout.beside e.targetSouth e.target) := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
  have hj := List.mem_range.mp hj
  apply Or.inr
  exact ⟨rank I (channel I j).target, 0, j, by unfold slots; omega, rfl⟩

private theorem choiceWires_terminalPin (I : Instance) {e : Wire} (he : e ∈ choiceWires I) :
    TerminalPinRow I (Layout.beside e.targetSouth e.target) := by
  obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
  obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
  have hj := List.mem_range.mp hj
  simp only [List.mem_ite_nil_right, List.mem_singleton] at he
  obtain ⟨_, rfl⟩ := he
  apply Or.inl
  refine ⟨j / 2, by omega, (if channelBit j then 49 else 41), ?_, ?_⟩
  all_goals cases channelBit j <;> simp [Layout.beside, DoorPinOffset]

private theorem skipWires_terminalPin (I : Instance) {e : Wire} (he : e ∈ skipWires I) :
    TerminalPinRow I (Layout.beside e.targetSouth e.target) := by
  obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
  obtain ⟨j, _, he⟩ := List.mem_flatMap.mp he
  simp only [List.mem_ite_nil_right, List.mem_singleton] at he
  obtain ⟨_, rfl⟩ := he
  exact Or.inr ⟨v, j + 1, 0, slots_pos I, rfl⟩

private theorem cleanupWires_terminalPin (I : Instance) {e : Wire} (he : e ∈ cleanupWires I) :
    TerminalPinRow I (Layout.beside e.targetSouth e.target) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
  have hi := List.mem_range.mp hi
  exact Or.inl ⟨i, hi, 71, by simp [DoorPinOffset], by simp [Layout.beside]⟩

theorem wires_terminalPin (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ (layout storage I).wires) :
    TerminalPinRow I (Layout.beside e.targetSouth e.target) := by
  simp only [layout, wires, List.mem_append] at he
  rcases he with (((he | he) | he) | he) | he
  · exact internalWires_terminalPin I he
  · exact arrivalWires_terminalPin I he
  · exact choiceWires_terminalPin I he
  · exact skipWires_terminalPin I he
  · cases storage
    · simp at he
    · exact cleanupWires_terminalPin I he

/-- First and last wire pins never share their chamber-stack row. -/
theorem wire_source_ne_terminalPin (storage : Bool) (I : Instance) {e f : Wire}
    (he : e ∈ (layout storage I).wires) (hf : f ∈ (layout storage I).wires) :
    e.source ≠ Layout.beside f.targetSouth f.target := by
  intro heq
  exact launch_terminal_disjoint I (heq ▸ wires_launch storage I he) (wires_terminalPin storage I hf)

end PushPuzzle.PushPush.Doors.Source
