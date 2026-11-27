/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.CompilerBounds

/-! Literal source wires and their rack-backed input slots. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors.Source

theorem internal_mem_wires (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ internalWires I) :
    e ∈ (layout storage I).wires := by
  simp only [layout, wires, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl he)))

private theorem arrival_mem_wires (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ arrivalWires I) :
    e ∈ (layout storage I).wires := by
  simp only [layout, wires, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr he)))

private theorem choice_mem_wires (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ choiceWires I) :
    e ∈ (layout storage I).wires := by
  simp only [layout, wires, List.mem_append]
  exact Or.inl (Or.inl (Or.inr he))

private theorem skip_mem_wires (storage : Bool) (I : Instance) {e : Wire} (he : e ∈ skipWires I) :
    e ∈ (layout storage I).wires := by
  simp only [layout, wires, List.mem_append]
  exact Or.inl (Or.inr he)

theorem internal_wire_mem (storage : Bool) (I : Instance) (i : Fin I.doors.length) {e : Wire}
    (he : e ∈ ([⟨doorBase i.val + 39, false, doorBase i.val + 80, true⟩,
      ⟨doorBase i.val + 79, false, doorBase i.val + 60, false⟩,
      ⟨doorBase i.val + 51, true, doorBase i.val + 10, false⟩,
      ⟨doorBase i.val + 11, true, doorBase i.val + 30, true⟩] : List Wire)) :
    e ∈ (layout storage I).wires := by
  apply internal_mem_wires
  exact List.mem_flatMap.mpr ⟨i.val, List.mem_range.mpr i.isLt, he⟩

theorem arrival_wire_mem (storage : Bool) (I : Instance) (j : ℕ) (hj : j < 2 * I.doors.length) :
    arrivalWire I j ∈ (layout storage I).wires := by
  apply arrival_mem_wires
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

theorem choice_wire_mem (storage : Bool) (I : Instance) (v j : ℕ)
    (hv : v < (labels I).length) (hj : j < 2 * I.doors.length)
    (hnot : v ≠ rank I I.target) (hsource : rank I (channel I j).source = v) :
    (⟨upperRow I v j, true, doorBase (j / 2) + (if channelBit j then 50 else 40),
      !channelBit j⟩ : Wire) ∈ (layout storage I).wires := by
  apply choice_mem_wires
  apply List.mem_flatMap.mpr
  refine ⟨v, List.mem_range.mpr hv, ?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨j, List.mem_range.mpr hj, by simp [hnot, hsource]⟩

theorem skip_wire_mem (storage : Bool) (I : Instance) (v j : ℕ)
    (hv : v < (labels I).length) (hj : j < 2 * I.doors.length) (hnot : v ≠ rank I I.target) :
    (⟨lowerRow I v j, false, inputRow I v (j + 1) 0, true⟩ : Wire) ∈ (layout storage I).wires := by
  apply skip_mem_wires
  apply List.mem_flatMap.mpr
  refine ⟨v, List.mem_range.mpr hv, ?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨j, List.mem_range.mpr hj, by simp [hnot]⟩

private theorem cleanup_mem_wires (I : Instance) {e : Wire} (he : e ∈ cleanupWires I) :
    e ∈ (layout true I).wires := by
  simp only [layout, wires, List.mem_append, ite_true]
  exact Or.inr he

theorem cleanup_wire_mem (I : Instance) (i : Fin I.doors.length) :
    (⟨if i.val = 0 then targetRow I else doorBase (i.val - 1) + 69,
      decide (i.val = 0), doorBase i.val + 70, true⟩ : Wire) ∈ (layout true I).wires := by
  apply cleanup_mem_wires
  exact List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩

private theorem room_index_bound (I : Instance) {v j : ℕ}
    (hv : v < (labels I).length) (hj : j < slots I) : slots I * v + j < roomCount I := by
  have hm : slots I * v + slots I ≤ slots I * (labels I).length := by
    simpa only [Nat.mul_succ] using Nat.mul_le_mul_left (slots I) (Nat.succ_le_of_lt hv)
  unfold roomCount
  rw [Nat.mul_comm (labels I).length]
  omega

theorem door_slot_rack_mem (storage : Bool) (I : Instance) {i offset : ℕ}
    (hi : i < I.doors.length) (hoff : offset ∈ ([10, 30, 40, 50, 60, 80] : List ℕ)) :
    doorBase i + offset ∈ (layout storage I).rackRows := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_range.mpr hi, ?_⟩
  apply List.mem_map.mpr
  exact ⟨offset, List.mem_append_left _ hoff, rfl⟩

private theorem door_erase_rack_mem (I : Instance) {i : ℕ} (hi : i < I.doors.length) :
    doorBase i + 70 ∈ (layout true I).rackRows := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_range.mpr hi, ?_⟩
  apply List.mem_map.mpr
  exact ⟨70, by simp, rfl⟩

theorem junction_input_rack_mem (storage : Bool) (I : Instance) {v j p : ℕ}
    (hv : v < (labels I).length) (hj : j < slots I) (hp : p < slots I) :
    inputRow I v j p ∈ (layout storage I).rackRows := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨slots I * v + j, List.mem_range.mpr (room_index_bound I hv hj), ?_⟩
  apply List.mem_map.mpr
  exact ⟨p, List.mem_range.mpr hp, rfl⟩

/-- Every actual wire ends at an ordinary rack-backed input. -/
theorem wire_target_rack_mem (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ (layout storage I).wires) : e.target ∈ (layout storage I).rackRows := by
  simp only [layout, wires, List.mem_append] at he
  rcases he with (((he | he) | he) | he) | he
  · obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
    have hi := List.mem_range.mp hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> exact door_slot_rack_mem storage I hi (by simp)
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
    have hj := List.mem_range.mp hj
    exact junction_input_rack_mem storage I (rank_bound I (channel_target_mem I hj))
      (slots_pos I) (by unfold slots; omega)
  · obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
    obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
    have hj := List.mem_range.mp hj
    simp only [List.mem_ite_nil_right, List.mem_singleton] at he
    obtain ⟨_, rfl⟩ := he
    apply door_slot_rack_mem storage I (by omega : j / 2 < I.doors.length)
    split <;> simp
  · obtain ⟨v, hv, he⟩ := List.mem_flatMap.mp he
    obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
    have hv := List.mem_range.mp hv
    have hj := List.mem_range.mp hj
    simp only [List.mem_ite_nil_right, List.mem_singleton] at he
    obtain ⟨_, rfl⟩ := he
    exact junction_input_rack_mem storage I hv (by unfold slots; omega) (slots_pos I)
  · cases storage
    · simp at he
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
      exact door_erase_rack_mem I (List.mem_range.mp hi)

end PushPuzzle.PushPush.Doors.Source
