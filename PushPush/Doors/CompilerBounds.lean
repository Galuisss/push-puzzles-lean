/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.CompilerInstance
public import PushPush.Doors.LayoutBounds
public import PushPush.Boundary
import Mathlib.Data.List.GetD

/-! All source-generated physical boxes and wire corners fit strictly inside the board. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

theorem rank_bound (I : Instance) {v : ℕ} (hv : v ∈ labels I) :
    rank I v < (labels I).length := by
  rw [length_labels]
  exact rank_lt I hv

theorem channel_target_mem (I : Instance) {j : ℕ} (hj : j < 2 * I.doors.length) :
    (channel I j).target ∈ labels I := by
  have hi : j / 2 < I.doors.length := by omega
  unfold channel
  rw [List.getD_eq_getElem _ _ hi]
  exact tunnel_target_mem I ⟨j / 2, hi⟩ _

theorem doorRow_fit (storage : Bool) (I : Instance) {i offset : ℕ}
    (hi : i < I.doors.length) (ho : offset < 90) :
    doorBase i + offset ≤ (layout storage I).depth := by
  have := door_row_before I hi ho
  change doorBase i + offset ≤ 90 * I.doors.length + _
  omega

theorem inputRow_fit (storage : Bool) (I : Instance) {v j p : ℕ}
    (hv : v < (labels I).length) (hj : j < slots I) (hp : p < slots I) :
    inputRow I v j p ≤ (layout storage I).depth := by
  unfold inputRow
  rw [Nat.add_assoc]
  apply room_row_fit storage I hv hj
  unfold chamberHeight
  omega

theorem upperRow_fit (storage : Bool) (I : Instance) {v j : ℕ}
    (hv : v < (labels I).length) (hj : j < slots I) :
    upperRow I v j ≤ (layout storage I).depth := by
  apply room_row_fit storage I hv hj
  have := chamberHeight_ge I
  omega

theorem lowerRow_fit (storage : Bool) (I : Instance) {v j : ℕ}
    (hv : v < (labels I).length) (hj : j < slots I) :
    lowerRow I v j ≤ (layout storage I).depth := by
  have hh := chamberHeight_ge I
  have he := room_row_fit storage I hv hj (by omega : chamberHeight I - 3 < chamberHeight I)
  unfold lowerRow
  omega

private theorem internalWires_fit (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ internalWires I) :
    e.source ≤ (layout storage I).depth ∧ e.target ≤ (layout storage I).depth := by
  obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
  have hi := List.mem_range.mp hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> constructor <;>
    exact doorRow_fit storage I hi (by omega)

private theorem arrivalWires_fit (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ arrivalWires I) :
    e.source ≤ (layout storage I).depth ∧ e.target ≤ (layout storage I).depth := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
  have hj := List.mem_range.mp hj
  constructor
  · apply doorRow_fit storage I (by omega : j / 2 < I.doors.length)
    split <;> omega
  · exact inputRow_fit storage I (rank_bound I (channel_target_mem I hj))
      (slots_pos I) (by unfold slots; omega)

private theorem choiceWires_fit (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ choiceWires I) :
    e.source ≤ (layout storage I).depth ∧ e.target ≤ (layout storage I).depth := by
  obtain ⟨v, hv, he⟩ := List.mem_flatMap.mp he
  obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
  have hv := List.mem_range.mp hv
  have hj := List.mem_range.mp hj
  simp only [List.mem_ite_nil_right, List.mem_singleton] at he
  obtain ⟨_, rfl⟩ := he
  constructor
  · exact upperRow_fit storage I hv (by unfold slots; omega)
  · apply doorRow_fit storage I (by omega : j / 2 < I.doors.length)
    split <;> omega

private theorem skipWires_fit (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ skipWires I) :
    e.source ≤ (layout storage I).depth ∧ e.target ≤ (layout storage I).depth := by
  obtain ⟨v, hv, he⟩ := List.mem_flatMap.mp he
  obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
  have hv := List.mem_range.mp hv
  have hj := List.mem_range.mp hj
  simp only [List.mem_ite_nil_right, List.mem_singleton] at he
  obtain ⟨_, rfl⟩ := he
  constructor
  · exact lowerRow_fit storage I hv (by unfold slots; omega)
  · exact inputRow_fit storage I hv (by unfold slots; omega) (slots_pos I)

private theorem cleanupWires_fit (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ cleanupWires I) :
    e.source ≤ (layout storage I).depth ∧ e.target ≤ (layout storage I).depth := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
  have hi := List.mem_range.mp hi
  constructor
  · by_cases hz : i = 0
    · simpa only [ite_eq_left hz] using targetRow_fit storage I
    · simp only [ite_eq_right hz]
      exact doorRow_fit storage I (by omega : i - 1 < I.doors.length) (by omega : 69 < 90)
  · exact doorRow_fit storage I hi (by omega : 70 < 90)

/-- Every actual wire endpoint lies in its original door or junction chamber. -/
theorem wires_fit (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ (layout storage I).wires) :
    e.source ≤ (layout storage I).depth ∧ e.target ≤ (layout storage I).depth := by
  simp only [layout, wires, List.mem_append] at he
  rcases he with (((he | he) | he) | he) | he
  · exact internalWires_fit storage I he
  · exact arrivalWires_fit storage I he
  · exact choiceWires_fit storage I he
  · exact skipWires_fit storage I he
  · cases storage
    · simp at he
    · exact cleanupWires_fit true I he

private theorem rackRows_fit (storage : Bool) (I : Instance) {y : ℕ}
    (hy : y ∈ (layout storage I).rackRows) : y ≤ (layout storage I).depth := by
  simp only [layout, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hy
  rcases hy with ⟨i, hi, offset, ho, rfl⟩ | ⟨j, hj, p, hp, rfl⟩
  · apply doorRow_fit storage I hi
    cases storage <;> simp_all <;> omega
  · have hm : chamberHeight I * j + chamberHeight I ≤ chamberHeight I * roomCount I := by
      simpa only [Nat.mul_succ] using
        Nat.mul_le_mul_left (chamberHeight I) (Nat.succ_le_of_lt hj)
    have ho : 10 + 8 * p < chamberHeight I := by unfold chamberHeight; omega
    change 90 * I.doors.length + chamberHeight I * j + 10 + 8 * p ≤
      90 * I.doors.length + chamberHeight I * roomCount I
    omega

theorem dividers_fit (storage : Bool) (I : Instance) {y : ℕ}
    (hy : y ∈ (layout storage I).dividers) : y ≤ (layout storage I).depth := by
  simp only [layout, List.mem_append, List.mem_map, List.mem_range] at hy
  rcases hy with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · have he := doorRow_fit storage I hi (by omega : 0 < 90)
    simpa only [Nat.add_zero] using he
  · have hm := Nat.mul_le_mul_left (chamberHeight I) (show j ≤ roomCount I by omega)
    change 90 * I.doors.length + chamberHeight I * j ≤
      90 * I.doors.length + chamberHeight I * roomCount I
    omega

theorem caps_fit (storage : Bool) (I : Instance) {y : ℕ}
    (hy : y ∈ (layout storage I).caps) : y ≤ (layout storage I).depth := by
  obtain ⟨v, hv, hy⟩ := List.mem_flatMap.mp hy
  obtain ⟨j, hj, hy⟩ := List.mem_flatMap.mp hy
  have hv := List.mem_range.mp hv
  have hj := List.mem_range.mp hj
  have hh := chamberHeight_ge I
  simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at hy
  rcases hy with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact room_row_fit storage I hv hj (by omega : 2 < chamberHeight I)
  · have he := room_row_fit storage I hv hj (by omega : chamberHeight I - 2 < chamberHeight I)
    omega

/-- The complete emitted recipe has all room coordinates within its declared stack. -/
theorem layout_fits (storage : Bool) (I : Instance) : (layout storage I).Fits where
  rack := fun _ hy => rackRows_fit storage I hy
  dividers := fun _ hy => dividers_fit storage I hy
  caps := fun _ hy => caps_fit storage I hy
  dataRows := fun _ hy => (layout_balanced storage I).initial_fit _ (List.mem_cons_of_mem _ hy)
  goalRows := fun _ hy => (layout_balanced storage I).goal_fit _ (List.mem_cons_of_mem _ hy)
  launch := launch_fit storage I
  stop := stop_fit storage I
  wires := fun _ he => wires_fit storage I he

/-- Exact storage targets have an empty true boundary on every compiled network. -/
theorem goals_interior (storage : Bool) (I : Instance)
    {s : PushFS.State (puzzle storage I).width (puzzle storage I).height}
    (hs : s.boxes = (puzzle storage I).board.goals) : Interior s := by
  intro p hp hb
  rw [hs] at hp
  have hi := (layout_fits storage I).goalsRaw_interior
    (((layout storage I).mem_raster _ _).mp hp)
  simp only [Boundary] at hb
  have hw := puzzle_width storage I
  have hh := puzzle_height storage I
  omega

end PushPuzzle.PushPush.Doors.Source
