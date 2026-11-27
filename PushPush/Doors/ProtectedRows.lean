/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.CompilerBalance

/-! Separation of rack holes, dividers, end caps and exact-target signal rows. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors

namespace Layout

theorem rackX_ge (L : Layout) : 40 ≤ L.rackX := by unfold rackX; omega

theorem shift_ge (L : Layout) : 15 ≤ L.shift := by unfold shift; omega

theorem initialRaw_rack_iff (L : Layout) (z : ℕ) :
    (L.rackX, z) ∈ L.initialRaw ↔ (L.rackX, z) ∈ L.rack := by
  constructor
  · intro hp
    have hr := L.rackX_ge
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_union.mp hp with hp | hp
        · have hx := L.pins_west hp; dsimp at hx; omega
        · exact hp
      · have hx := L.blockers_column hp; dsimp at hx; omega
    · obtain ⟨y, _, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
      have hx := congrArg Prod.fst he
      dsimp at hx
      omega
  · intro hp
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hp))

theorem goalsRaw_rack_iff (L : Layout) (z : ℕ) :
    (L.rackX, z) ∈ L.goalsRaw ↔ (L.rackX, z) ∈ L.rack := by
  constructor
  · intro hp
    have hr := L.rackX_ge
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_union.mp hp with hp | hp
        · have hx := L.pins_west hp; dsimp at hx; omega
        · exact hp
      · have hx := L.blockers_column hp; dsimp at hx; omega
    · obtain ⟨y, _, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
      have hx := congrArg Prod.fst he
      dsimp at hx
      omega
  · intro hp
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hp))

theorem mem_rack_iff (L : Layout) (z : ℕ) :
    (L.rackX, z) ∈ L.rack ↔
      (∃ y ∈ L.rackRows, z = y + L.shift) ∨
        ∃ y ∈ L.dividers, z = y + L.shift - 1 ∨ z = y + L.shift + 1 := by
  simp only [rack, List.mem_toFinset, List.mem_append, List.mem_map, List.mem_flatMap,
    List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, true_and]
  aesop

private theorem goalsRaw_working_iff (L : Layout) (z : ℕ) :
    (L.rackX - 1, z) ∈ L.goalsRaw ↔
      ∃ y ∈ L.dividers ++ L.caps ++ L.stop :: L.goalRows, z = y + L.shift := by
  have hr := L.rackX_ge
  have hpin : (L.rackX - 1, z) ∉ L.pins := by
    intro hp
    have hx := L.pins_west hp
    dsimp at hx
    omega
  have hrack : (L.rackX - 1, z) ∉ L.rack := by
    intro hp
    have hx := L.rack_column hp
    dsimp at hx
    omega
  simp only [goalsRaw, fixed, Finset.mem_union, hpin, hrack, false_or, blockers,
    List.mem_toFinset, List.mem_map, Prod.mk.injEq, true_and, List.mem_append]
  aesop

end Layout

namespace Source

private theorem scaled_gap {r a b offset : ℕ} (hlo : 2 ≤ offset) (hhi : offset + 2 ≤ r) :
    r * b + 1 < r * a + offset ∨ r * a + offset + 1 < r * b := by
  by_cases hab : b ≤ a
  · have hm := Nat.mul_le_mul_left r hab
    exact Or.inl (by omega)
  · have hm := Nat.mul_le_mul_left r (show a + 1 ≤ b by omega)
    simp only [Nat.mul_succ] at hm
    exact Or.inr (by omega)

private theorem scaled_nonunit {r a b : ℕ} (hr : 2 ≤ r) : r * a + 1 ≠ r * b := by
  intro he
  by_cases hab : b ≤ a
  · have hm := Nat.mul_le_mul_left r hab
    omega
  · have hm := Nat.mul_le_mul_left r (show a + 1 ≤ b by omega)
    simp only [Nat.mul_succ] at hm
    omega

theorem door_row_divider_gap (storage : Bool) (I : Instance) {i offset g : ℕ}
    (hi : i < I.doors.length) (hlo : 2 ≤ offset) (hhi : offset + 2 ≤ 90)
    (hg : g ∈ (layout storage I).dividers) :
    g + 1 < doorBase i + offset ∨ doorBase i + offset + 1 < g := by
  rcases mem_dividers storage I hg with ⟨j, _, rfl⟩ | ⟨j, rfl⟩
  · exact scaled_gap hlo hhi
  · apply Or.inr
    unfold doorBase
    omega

theorem room_row_divider_gap (storage : Bool) (I : Instance) (v j : ℕ) {offset g : ℕ}
    (hlo : 2 ≤ offset) (hhi : offset + 2 ≤ chamberHeight I)
    (hg : g ∈ (layout storage I).dividers) :
    g + 1 < roomBase I v j + offset ∨ roomBase I v j + offset + 1 < g := by
  rcases mem_dividers storage I hg with ⟨i, hi, rfl⟩ | ⟨k, rfl⟩
  · apply Or.inl
    unfold doorBase roomBase
    omega
  · have hh := scaled_gap (r := chamberHeight I) (a := slots I * v + j) (b := k) hlo hhi
    unfold roomBase
    omega

private theorem dividers_no_neighbor (storage : Bool) (I : Instance) {g f : ℕ}
    (hg : g ∈ (layout storage I).dividers) (hf : f ∈ (layout storage I).dividers) :
    g + 1 ≠ f := by
  have hh := chamberHeight_ge I
  rcases mem_dividers storage I hg with ⟨i, hi, rfl⟩ | ⟨j, rfl⟩ <;>
    rcases mem_dividers storage I hf with ⟨i', hi', rfl⟩ | ⟨j', rfl⟩
  · unfold doorBase
    omega
  · unfold doorBase
    omega
  · unfold doorBase
    omega
  · intro he
    have he' : chamberHeight I * j + 1 = chamberHeight I * j' := by omega
    exact scaled_nonunit (by omega : 2 ≤ chamberHeight I) he'

private theorem caps_divider_gap (storage : Bool) (I : Instance) {y g : ℕ}
    (hy : y ∈ (layout storage I).caps) (hg : g ∈ (layout storage I).dividers) :
    g + 1 < y ∨ y + 1 < g := by
  have hh := chamberHeight_ge I
  obtain ⟨j, he | he⟩ := mem_caps storage I hy
  · have hgap := room_row_divider_gap storage I 0 j (offset := 2) (by omega) (by omega) hg
    simp only [roomBase, Nat.mul_zero, Nat.zero_add] at hgap
    omega
  · have hgap := room_row_divider_gap storage I 0 j (offset := chamberHeight I - 2)
      (by omega) (by omega) hg
    simp only [roomBase, Nat.mul_zero, Nat.zero_add] at hgap
    omega

private theorem rackRows_free (storage : Bool) (I : Instance) {y : ℕ}
    (hy : y ∈ (layout storage I).rackRows) :
    y ∉ (layout storage I).dividers ++ (layout storage I).caps := by
  simp only [layout, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hy
  rcases hy with ⟨i, hi, offset, ho, rfl⟩ | ⟨j, _, p, hp, rfl⟩
  · have hoff : 0 < offset ∧ offset < 90 := by cases storage <;> simp_all <;> omega
    exact door_row_free storage I hi hoff.1 hoff.2
  · have hlo : 2 < 10 + 8 * p := by omega
    have hhi : 10 + 8 * p + 2 < chamberHeight I := by unfold chamberHeight; omega
    simpa only [roomBase, Nat.mul_zero, Nat.zero_add, Nat.add_assoc] using
      room_row_free storage I 0 j hlo hhi

private theorem dataRows_divider_gap (storage : Bool) (I : Instance) {y g : ℕ}
    (hy : y ∈ dataRows I) (hg : g ∈ (layout storage I).dividers) :
    g + 1 < y ∨ y + 1 < g := by
  obtain ⟨i, rfl⟩ := dataRows_mem I hy
  apply door_row_divider_gap storage I i.isLt ?_ ?_ hg <;> split <;> omega

private theorem goalRows_divider_gap (storage : Bool) (I : Instance) {y g : ℕ}
    (hy : y ∈ (layout storage I).goalRows) (hg : g ∈ (layout storage I).dividers) :
    g + 1 < y ∨ y + 1 < g := by
  cases storage
  · exact dataRows_divider_gap false I hy hg
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    exact door_row_divider_gap true I (List.mem_range.mp hi) (by omega) (by omega) hg

theorem stop_divider_gap (storage : Bool) (I : Instance) {g : ℕ}
    (hg : g ∈ (layout storage I).dividers) :
    g + 1 < (layout storage I).stop ∨ (layout storage I).stop + 1 < g := by
  have hh := chamberHeight_ge I
  have htarget : g + 1 < targetRow I ∨ targetRow I + 1 < g :=
    room_row_divider_gap storage I (rank I I.target) 0 (by omega) (by omega) hg
  cases storage
  · exact htarget
  · by_cases hd : 0 < I.doors.length
    · have hstop := door_row_divider_gap true I (i := I.doors.length - 1) (offset := 69)
        (by omega) (by omega) (by omega) hg
      simpa only [layout, Bool.true_and, decide_eq_true_eq, ite_eq_left hd] using hstop
    · simpa only [layout, Bool.true_and, decide_eq_true_eq, ite_eq_right hd] using htarget

theorem target_rows_no_neighbor (storage : Bool) (I : Instance) {y g : ℕ}
    (hy : y ∈ (layout storage I).dividers ++ (layout storage I).caps ++
      (layout storage I).stop :: (layout storage I).goalRows)
    (hg : g ∈ (layout storage I).dividers) : y + 1 ≠ g ∧ g + 1 ≠ y := by
  simp only [List.mem_append, List.mem_cons] at hy
  rcases hy with (hy | hy) | (rfl | hy)
  · exact ⟨dividers_no_neighbor storage I hy hg, dividers_no_neighbor storage I hg hy⟩
  · have hgap := caps_divider_gap storage I hy hg
    omega
  · have hgap := stop_divider_gap storage I hg
    omega
  · have hgap := goalRows_divider_gap storage I hy hg
    omega

theorem divider_rack_empty (storage : Bool) (I : Instance) {g : ℕ}
    (hg : g ∈ (layout storage I).dividers) :
    ((layout storage I).rackX, g + (layout storage I).shift) ∉ (layout storage I).rack := by
  intro hp
  have hshift := (layout storage I).shift_ge
  rcases ((layout storage I).mem_rack_iff _).mp hp with ⟨y, hy, he⟩ | ⟨y, hy, he | he⟩
  · have hey : y = g := by omega
    subst y
    exact rackRows_free storage I hy (List.mem_append_left _ hg)
  · exact dividers_no_neighbor storage I hg hy (by omega)
  · exact dividers_no_neighbor storage I hy hg (by omega)

theorem divider_rack_neighbors (storage : Bool) (I : Instance) {g : ℕ}
    (hg : g ∈ (layout storage I).dividers) :
    ((layout storage I).rackX, g + (layout storage I).shift - 1) ∈ (layout storage I).rack ∧
      ((layout storage I).rackX, g + (layout storage I).shift + 1) ∈ (layout storage I).rack := by
  exact ⟨((layout storage I).mem_rack_iff _).mpr (Or.inr ⟨g, hg, Or.inl rfl⟩),
    ((layout storage I).mem_rack_iff _).mpr (Or.inr ⟨g, hg, Or.inr rfl⟩)⟩

theorem cap_rack_empty (storage : Bool) (I : Instance) {y : ℕ}
    (hy : y ∈ (layout storage I).caps) :
    ((layout storage I).rackX, y + (layout storage I).shift) ∉ (layout storage I).rack := by
  intro hp
  have hshift := (layout storage I).shift_ge
  rcases ((layout storage I).mem_rack_iff _).mp hp with ⟨z, hz, he⟩ | ⟨g, hg, he | he⟩
  · have hez : z = y := by omega
    subst z
    exact rackRows_free storage I hz (List.mem_append_right _ hy)
  · have hgap := caps_divider_gap storage I hy hg
    omega
  · have hgap := caps_divider_gap storage I hy hg
    omega

theorem divider_goal_mem (storage : Bool) (I : Instance) {g : ℕ}
    (hg : g ∈ (layout storage I).dividers) :
    ((layout storage I).rackX - 1, g + (layout storage I).shift) ∈
      (layout storage I).goalsRaw := by
  apply ((layout storage I).goalsRaw_working_iff _).mpr
  exact ⟨g, List.mem_append_left _ (List.mem_append_left _ hg), rfl⟩

theorem divider_goal_neighbors (storage : Bool) (I : Instance) {g : ℕ}
    (hg : g ∈ (layout storage I).dividers) :
    ((layout storage I).rackX - 1, g + (layout storage I).shift - 1) ∉
        (layout storage I).goalsRaw ∧
      ((layout storage I).rackX - 1, g + (layout storage I).shift + 1) ∉
        (layout storage I).goalsRaw := by
  have hshift := (layout storage I).shift_ge
  constructor <;> intro hp <;>
    obtain ⟨y, hy, he⟩ := ((layout storage I).goalsRaw_working_iff _).mp hp
  · have hh := target_rows_no_neighbor storage I hy hg
    omega
  · have hh := target_rows_no_neighbor storage I hy hg
    omega

theorem cap_goal_mem (storage : Bool) (I : Instance) {y : ℕ}
    (hy : y ∈ (layout storage I).caps) :
    ((layout storage I).rackX - 1, y + (layout storage I).shift) ∈
      (layout storage I).goalsRaw := by
  apply ((layout storage I).goalsRaw_working_iff _).mpr
  exact ⟨y, List.mem_append_left _ (List.mem_append_right _ hy), rfl⟩

theorem room_index_lt (I : Instance) {v j : ℕ} (hv : v < (labels I).length)
    (hj : j < slots I) : slots I * v + j < roomCount I := by
  have hm : slots I * v + slots I ≤ slots I * (labels I).length := by
    simpa only [Nat.mul_succ] using Nat.mul_le_mul_left (slots I) (Nat.succ_le_of_lt hv)
  unfold roomCount
  rw [Nat.mul_comm (labels I).length]
  omega

theorem cap_divider_gap_two (storage : Bool) (I : Instance) {y : ℕ}
    (hy : y ∈ (layout storage I).caps) :
    ∃ g ∈ (layout storage I).dividers, y = g + 2 ∨ g = y + 2 := by
  obtain ⟨v, hv, hy⟩ := List.mem_flatMap.mp hy
  obtain ⟨j, hj, hy⟩ := List.mem_flatMap.mp hy
  have hindex := room_index_lt I (List.mem_range.mp hv) (List.mem_range.mp hj)
  simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at hy
  have hbase : roomBase I v j ∈ (layout storage I).dividers := by
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨slots I * v + j, List.mem_range.mpr (by omega), rfl⟩
  rcases hy with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨roomBase I v j, hbase, Or.inl rfl⟩
  · have hnext : roomBase I v j + chamberHeight I ∈ (layout storage I).dividers := by
      apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨slots I * v + j + 1, List.mem_range.mpr (by omega), ?_⟩
      simp only [roomBase, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    refine ⟨roomBase I v j + chamberHeight I, hnext, Or.inr ?_⟩
    have hh := chamberHeight_ge I
    omega

end Source
end PushPuzzle.PushPush.Doors
