/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.Compiler
public import PushPush.Doors.LayoutBalance

/-! Distinct mobile slots and equal exact-storage inventories of the actual compiler. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

private theorem uniform_index {r a b u v : ℕ} (hu : u < r) (hv : v < r)
    (he : r * a + u = r * b + v) : a = b ∧ u = v := by
  have hab : a = b := by
    by_contra h
    rcases Nat.lt_or_gt_of_ne h with h | h
    · have hm : r * a + r ≤ r * b := by
        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left r (Nat.succ_le_of_lt h)
      omega
    · have hm : r * b + r ≤ r * a := by
        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left r (Nat.succ_le_of_lt h)
      omega
  exact ⟨hab, by subst b; omega⟩

theorem mem_dividers (storage : Bool) (I : Instance) {y : ℕ}
    (hy : y ∈ (layout storage I).dividers) :
    (∃ i < I.doors.length, y = doorBase i) ∨
      ∃ j, y = 90 * I.doors.length + chamberHeight I * j := by
  simp only [layout, List.mem_append, List.mem_map, List.mem_range] at hy
  rcases hy with ⟨i, hi, rfl⟩ | ⟨j, _, rfl⟩
  · exact Or.inl ⟨i, hi, rfl⟩
  · exact Or.inr ⟨j, rfl⟩

theorem mem_caps (storage : Bool) (I : Instance) {y : ℕ}
    (hy : y ∈ (layout storage I).caps) :
    ∃ j, y = 90 * I.doors.length + chamberHeight I * j + 2 ∨
      y = 90 * I.doors.length + chamberHeight I * j + chamberHeight I - 2 := by
  obtain ⟨v, _, hy⟩ := List.mem_flatMap.mp hy
  obtain ⟨j, _, hy⟩ := List.mem_flatMap.mp hy
  simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at hy
  refine ⟨slots I * v + j, ?_⟩
  rcases hy with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem door_row_before (I : Instance) {i offset : ℕ} (hi : i < I.doors.length)
    (ho : offset < 90) : doorBase i + offset < 90 * I.doors.length := by
  unfold doorBase
  omega

theorem door_row_free (storage : Bool) (I : Instance) {i offset : ℕ}
    (hi : i < I.doors.length) (hpos : 0 < offset) (ho : offset < 90) :
    doorBase i + offset ∉ (layout storage I).dividers ++ (layout storage I).caps := by
  intro hy
  have hb := door_row_before I hi ho
  have hh := chamberHeight_ge I
  rcases List.mem_append.mp hy with hd | hc
  · rcases mem_dividers storage I hd with ⟨j, _, he⟩ | ⟨j, he⟩
    · have hu := uniform_index ho (by omega : 0 < 90) (by
        simpa [doorBase] using he)
      omega
    · omega
  · obtain ⟨j, he | he⟩ := mem_caps storage I hc <;> omega

theorem room_row_free (storage : Bool) (I : Instance) (v j : ℕ) {offset : ℕ}
    (hlo : 2 < offset) (hhi : offset + 2 < chamberHeight I) :
    roomBase I v j + offset ∉ (layout storage I).dividers ++ (layout storage I).caps := by
  intro hy
  have hh := chamberHeight_ge I
  rcases List.mem_append.mp hy with hd | hc
  · rcases mem_dividers storage I hd with ⟨i, hi, he⟩ | ⟨k, he⟩
    · unfold roomBase doorBase at he
      omega
    · have he' : chamberHeight I * (slots I * v + j) + offset = chamberHeight I * k + 0 := by
        unfold roomBase at he
        omega
      have hu := uniform_index (by omega : offset < chamberHeight I) (by omega) he'
      omega
  · obtain ⟨k, he | he⟩ := mem_caps storage I hc
    · have he' : chamberHeight I * (slots I * v + j) + offset = chamberHeight I * k + 2 := by
        unfold roomBase at he
        omega
      have hu := uniform_index (by omega : offset < chamberHeight I) (by omega) he'
      omega
    · have he' : chamberHeight I * (slots I * v + j) + offset =
          chamberHeight I * k + (chamberHeight I - 2) := by
        unfold roomBase at he
        omega
      have hu := uniform_index (by omega : offset < chamberHeight I) (by omega) he'
      omega

theorem room_row_fit (storage : Bool) (I : Instance) {v j offset : ℕ}
    (hv : v < (labels I).length) (hj : j < slots I) (ho : offset < chamberHeight I) :
    roomBase I v j + offset ≤ (layout storage I).depth := by
  have hn : slots I * v + j < roomCount I := by
    have hm : slots I * v + slots I ≤ slots I * (labels I).length := by
      simpa only [Nat.mul_succ] using Nat.mul_le_mul_left (slots I) (Nat.succ_le_of_lt hv)
    unfold roomCount
    rw [Nat.mul_comm (labels I).length]
    omega
  have hm : chamberHeight I * (slots I * v + j) + chamberHeight I ≤
      chamberHeight I * roomCount I := by
    simpa only [Nat.mul_succ] using Nat.mul_le_mul_left (chamberHeight I) (Nat.succ_le_of_lt hn)
  change 90 * I.doors.length + chamberHeight I * (slots I * v + j) + offset ≤
    90 * I.doors.length + chamberHeight I * roomCount I
  omega

theorem dataRows_mem (I : Instance) {y : ℕ} (hy : y ∈ dataRows I) :
    ∃ i : Fin I.doors.length, y = doorBase i.val + if I.doors[i].initial then 60 else 30 := by
  obtain ⟨⟨e, i⟩, he, rfl⟩ := List.mem_map.mp hy
  obtain ⟨hi, hee⟩ := List.mem_zipIdx' he
  refine ⟨⟨i, hi⟩, ?_⟩
  dsimp
  rw [hee]

private theorem dataRows_nodup (I : Instance) : (dataRows I).Nodup := by
  apply List.nodup_iff_injective_getElem.mpr
  intro i j he
  have hi : i.val < I.doors.length := by simpa [dataRows_length] using i.isLt
  have hj : j.val < I.doors.length := by simpa [dataRows_length] using j.isLt
  simp only [dataRows, List.getElem_map, List.getElem_zipIdx, Nat.zero_add] at he
  have hio : (if I.doors[i.val].initial then 60 else 30) < 90 := by split <;> omega
  have hjo : (if I.doors[j.val].initial then 60 else 30) < 90 := by split <;> omega
  apply Fin.ext
  exact (uniform_index hio hjo he).1

private theorem dataRows_before (I : Instance) {y : ℕ} (hy : y ∈ dataRows I) :
    y < 90 * I.doors.length := by
  obtain ⟨i, rfl⟩ := dataRows_mem I hy
  apply door_row_before I i.isLt
  split <;> omega

private theorem dataRows_free (storage : Bool) (I : Instance) {y : ℕ} (hy : y ∈ dataRows I) :
    y ∉ (layout storage I).dividers ++ (layout storage I).caps := by
  obtain ⟨i, rfl⟩ := dataRows_mem I hy
  apply door_row_free storage I i.isLt <;> split <;> omega

private theorem launch_lower_bound (storage : Bool) (I : Instance) :
    90 * I.doors.length ≤ (layout storage I).launch := by
  change 90 * I.doors.length ≤ inputRow I (rank I I.start) 0 (2 * I.doors.length)
  unfold inputRow roomBase
  omega

theorem targetRow_lower_bound (I : Instance) : 90 * I.doors.length ≤ targetRow I := by
  unfold targetRow upperRow roomBase
  omega

private theorem launch_free (storage : Bool) (I : Instance) :
    (layout storage I).launch ∉ (layout storage I).dividers ++ (layout storage I).caps := by
  change roomBase I (rank I I.start) 0 + 10 + 8 * (2 * I.doors.length) ∉ _
  rw [Nat.add_assoc]
  apply room_row_free storage I (rank I I.start) 0
  · omega
  · unfold chamberHeight slots
    omega

theorem targetRow_free (storage : Bool) (I : Instance) :
    targetRow I ∉ (layout storage I).dividers ++ (layout storage I).caps := by
  apply room_row_free storage I (rank I I.target) 0 (by omega)
  have := chamberHeight_ge I
  omega

theorem launch_fit (storage : Bool) (I : Instance) :
    (layout storage I).launch ≤ (layout storage I).depth := by
  change roomBase I (rank I I.start) 0 + 10 + 8 * (2 * I.doors.length) ≤ _
  rw [Nat.add_assoc]
  apply room_row_fit storage I
  · rw [length_labels]
    exact rank_lt I (start_mem I)
  · exact slots_pos I
  · unfold chamberHeight slots
    omega

theorem targetRow_fit (storage : Bool) (I : Instance) :
    targetRow I ≤ (layout storage I).depth := by
  apply room_row_fit storage I
  · rw [length_labels]
    exact rank_lt I (target_mem I)
  · exact slots_pos I
  · have := chamberHeight_ge I
    omega

private theorem goalRows_nodup (storage : Bool) (I : Instance) :
    (layout storage I).goalRows.Nodup := by
  cases storage
  · exact dataRows_nodup I
  · apply (List.nodup_range (n := I.doors.length)).map
    intro i j he
    change 90 * i + 70 = 90 * j + 70 at he
    omega

private theorem goalRows_free (storage : Bool) (I : Instance) {y : ℕ}
    (hy : y ∈ (layout storage I).goalRows) :
    y ∉ (layout storage I).dividers ++ (layout storage I).caps := by
  cases storage
  · exact dataRows_free false I hy
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    exact door_row_free true I (List.mem_range.mp hi) (by omega) (by omega)

private theorem stop_free (storage : Bool) (I : Instance) :
    (layout storage I).stop ∉ (layout storage I).dividers ++ (layout storage I).caps := by
  cases storage
  · exact targetRow_free false I
  · by_cases hd : 0 < I.doors.length
    · have he : (layout true I).stop = doorBase (I.doors.length - 1) + 69 := by simp [layout, hd]
      rw [he]
      exact door_row_free true I (by omega) (by omega) (by omega)
    · simpa only [layout, Bool.true_and, decide_eq_true_eq, ite_eq_right hd] using targetRow_free true I

theorem stop_fit (storage : Bool) (I : Instance) :
    (layout storage I).stop ≤ (layout storage I).depth := by
  cases storage
  · exact targetRow_fit false I
  · by_cases hd : 0 < I.doors.length
    · change (if true && decide (0 < I.doors.length) then _ else _) ≤ _
      simp only [Bool.true_and, decide_eq_true_eq, ite_eq_left hd]
      have hb := door_row_before I (show I.doors.length - 1 < I.doors.length by omega)
        (by omega : 69 < 90)
      change doorBase (I.doors.length - 1) + 69 ≤ 90 * I.doors.length + _
      omega
    · simpa only [layout, Bool.true_and, decide_eq_true_eq, ite_eq_right hd] using targetRow_fit true I

private theorem stop_not_goalRows (storage : Bool) (I : Instance) :
    (layout storage I).stop ∉ (layout storage I).goalRows := by
  cases storage
  · intro hy
    have hb := dataRows_before I hy
    have hl := targetRow_lower_bound I
    exact (not_lt_of_ge hl) hb
  · by_cases hd : 0 < I.doors.length
    · intro hy
      obtain ⟨i, _, hi⟩ := List.mem_map.mp hy
      have he : doorBase i + 70 = doorBase (I.doors.length - 1) + 69 := by
        simpa [layout, hd] using hi
      have hu := uniform_index (by omega : 70 < 90) (by omega : 69 < 90) he
      omega
    · have hz : I.doors.length = 0 := by omega
      simp [layout, hz]

/-- Every source network yields a genuine equal-cardinality storage layout. -/
theorem layout_balanced (storage : Bool) (I : Instance) : (layout storage I).Balanced where
  initial_nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, dataRows_nodup I⟩
    intro hy
    have hb := dataRows_before I hy
    have hl := launch_lower_bound storage I
    omega
  goal_nodup := List.nodup_cons.mpr ⟨stop_not_goalRows storage I, goalRows_nodup storage I⟩
  initial_free := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact launch_free storage I
    · exact dataRows_free storage I hy
  goal_free := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact stop_free storage I
    · exact goalRows_free storage I hy
  initial_fit := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact launch_fit storage I
    · have hb := dataRows_before I hy
      change y ≤ 90 * I.doors.length + _
      omega
  goal_fit := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact stop_fit storage I
    · cases storage
      · have hb := dataRows_before I hy
        change y ≤ 90 * I.doors.length + _
        omega
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
        have hb := door_row_before I (List.mem_range.mp hi) (by omega : 70 < 90)
        change doorBase i + 70 ≤ 90 * I.doors.length + _
        omega
  count := (dataRows_length I).trans (goalRows_length storage I).symm

end PushPuzzle.PushPush.Doors.Source
