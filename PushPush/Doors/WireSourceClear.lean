/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireSourcePins
public import PushPush.Doors.ForwardSignal

/-! Empty launch supports and wired-input rows in actual source stocks. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors.Source

theorem roomBase_even (I : Instance) (v j : ℕ) : roomBase I v j % 2 = 0 := by
  simp [roomBase, chamberHeight, Nat.add_mod, Nat.mul_mod]

theorem inputRow_even (I : Instance) (v j p : ℕ) : inputRow I v j p % 2 = 0 := by
  simp [inputRow, roomBase_even, Nat.add_mod, Nat.mul_mod]

theorem LaunchRow.odd (I : Instance) {row : ℕ} (hr : LaunchRow I row) : row % 2 = 1 := by
  have hh := chamberHeight_ge I
  rcases hr with ⟨i, hi, a, ha, rfl⟩ | ⟨v, j, he | he⟩
  · simp only [DoorLaunchOffset] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [doorBase, Nat.add_mod, Nat.mul_mod]
  · rw [he]
    simp [upperRow, roomBase_even, Nat.add_mod]
  · have hr := roomBase_even I v j
    have hc : chamberHeight I % 2 = 0 := by simp [chamberHeight, Nat.add_mod, Nat.mul_mod]
    unfold lowerRow at he
    omega

theorem TerminalPinRow.odd (I : Instance) {row : ℕ} (hr : TerminalPinRow I row) : row % 2 = 1 := by
  rcases hr with ⟨i, hi, a, ha, rfl⟩ | ⟨v, j, p, hp, rfl⟩
  · simp only [DoorPinOffset] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [doorBase, Nat.add_mod, Nat.mul_mod]
  · simp [inputRow_even, Nat.add_mod]

private theorem wires_target_even (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ (layout storage I).wires) : e.target % 2 = 0 := by
  simp only [layout, wires, List.mem_append] at he
  rcases he with (((he | he) | he) | he) | he
  · obtain ⟨i, _, he⟩ := List.mem_flatMap.mp he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp [doorBase, Nat.add_mod, Nat.mul_mod]
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp he
    exact inputRow_even I _ _ _
  · obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
    obtain ⟨j, _, he⟩ := List.mem_flatMap.mp he
    simp only [List.mem_ite_nil_right, List.mem_singleton] at he
    obtain ⟨_, rfl⟩ := he
    dsimp
    split <;> simp [doorBase, Nat.add_mod, Nat.mul_mod]
  · obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
    obtain ⟨j, _, he⟩ := List.mem_flatMap.mp he
    simp only [List.mem_ite_nil_right, List.mem_singleton] at he
    obtain ⟨_, rfl⟩ := he
    exact inputRow_even I _ _ _
  · cases storage
    · simp at he
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
      simp [doorBase, Nat.add_mod, Nat.mul_mod]

/-- Routing pins never occupy a wired horizontal arrival row. -/
theorem pins_not_target_row (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ (layout storage I).wires) {p : ℕ × ℕ}
    (hp : p ∈ (layout storage I).pins) : p.2 ≠ e.target + (layout storage I).shift := by
  intro heq
  have ht := wires_target_even storage I he
  have hb := (wires_fit storage I he).2
  rcases pins_row_cases storage I hp with hout | ⟨f, hf, hs | hs⟩
  · omega
  · have hfodd := (wires_launch storage I hf).odd I
    omega
  · have hfodd := (wires_terminalPin storage I hf).odd I
    change (pinRow f) % 2 = 1 at hfodd
    omega

theorem rackRows_even (storage : Bool) (I : Instance) {row : ℕ}
    (hr : row ∈ (layout storage I).rackRows) : row % 2 = 0 := by
  simp only [layout, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hr
  rcases hr with ⟨i, hi, a, ha, rfl⟩ | ⟨j, hj, p, hp, rfl⟩
  · cases storage <;> simp at ha <;>
      simp [doorBase, Nat.add_mod, Nat.mul_mod] <;> omega
  · simp [chamberHeight, Nat.add_mod, Nat.mul_mod]

theorem LaunchRow.free (storage : Bool) (I : Instance) {row : ℕ} (hr : LaunchRow I row) :
    row ∉ (layout storage I).dividers ++ (layout storage I).caps := by
  have hh := chamberHeight_ge I
  rcases hr with ⟨i, hi, a, ha, rfl⟩ | ⟨v, j, he | he⟩
  · apply door_row_free storage I hi <;> simp only [DoorLaunchOffset] at ha <;> omega
  · rw [he]
    exact room_row_free storage I v j (by omega : 2 < 3) (by omega)
  · have he' : row = roomBase I v j + (chamberHeight I - 3) := by
      unfold lowerRow at he
      omega
    rw [he']
    exact room_row_free storage I v j (by omega : 2 < chamberHeight I - 3) (by omega)

theorem wires_target_free (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ (layout storage I).wires) :
    e.target ∉ (layout storage I).dividers ++ (layout storage I).caps := by
  have hh := chamberHeight_ge I
  simp only [layout, wires, List.mem_append] at he
  rcases he with (((he | he) | he) | he) | he
  · obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
    have hi := List.mem_range.mp hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> apply door_row_free storage I hi <;> omega
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
    have hj := List.mem_range.mp hj
    change roomBase I (rank I (channel I j).target) 0 + 10 + 8 * j ∉ _
    rw [Nat.add_assoc]
    apply room_row_free storage I (rank I (channel I j).target) 0
    · omega
    · unfold chamberHeight slots
      omega
  · obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
    obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
    have hj := List.mem_range.mp hj
    simp only [List.mem_ite_nil_right, List.mem_singleton] at he
    obtain ⟨_, rfl⟩ := he
    apply door_row_free storage I (by omega : j / 2 < I.doors.length) <;> split <;> omega
  · obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
    obtain ⟨j, _, he⟩ := List.mem_flatMap.mp he
    simp only [List.mem_ite_nil_right, List.mem_singleton] at he
    obtain ⟨_, rfl⟩ := he
    apply room_row_free storage I v (j + 1) <;> omega
  · cases storage
    · simp at he
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
      exact door_row_free true I (List.mem_range.mp hi) (by omega : 0 < 70) (by omega)

private theorem room_row_divider_neighbors (storage : Bool) (I : Instance) (v j a : ℕ)
    (hlo : 2 < a) (hhi : a + 2 < chamberHeight I) {g : ℕ}
    (hg : g ∈ (layout storage I).dividers) :
    roomBase I v j + a ≠ g + 1 ∧ roomBase I v j + a + 1 ≠ g := by
  have hh := chamberHeight_ge I
  rcases mem_dividers storage I hg with ⟨i, hi, rfl⟩ | ⟨k, rfl⟩
  · have hb := door_row_before I hi (by omega : 1 < 90)
    unfold roomBase doorBase at *
    omega
  · constructor
    · intro he
      have hu := row_address_injective (by omega : a < chamberHeight I)
        (by omega : 1 < chamberHeight I) (show chamberHeight I * (slots I * v + j) + a =
          chamberHeight I * k + 1 by unfold roomBase at he; omega)
      omega
    · intro he
      have hu := row_address_injective (by omega : a + 1 < chamberHeight I)
        (by omega : 0 < chamberHeight I) (show chamberHeight I * (slots I * v + j) + (a + 1) =
          chamberHeight I * k + 0 by unfold roomBase at he; omega)
      omega

theorem LaunchRow.divider_neighbors (storage : Bool) (I : Instance) {row g : ℕ}
    (hr : LaunchRow I row) (hg : g ∈ (layout storage I).dividers) :
    row ≠ g + 1 ∧ row + 1 ≠ g := by
  have hh := chamberHeight_ge I
  rcases hr with ⟨i, hi, a, ha, rfl⟩ | ⟨v, j, he | he⟩
  · simp only [DoorLaunchOffset] at ha
    rcases mem_dividers storage I hg with ⟨k, hk, rfl⟩ | ⟨k, rfl⟩ <;>
      dsimp [doorBase] <;> omega
  · rw [he]
    exact room_row_divider_neighbors storage I v j 3 (by omega) (by omega) hg
  · have he' : row = roomBase I v j + (chamberHeight I - 3) := by
      unfold lowerRow at he
      omega
    rw [he']
    exact room_row_divider_neighbors storage I v j (chamberHeight I - 3) (by omega) (by omega) hg

/-- The player's eastern support on any launch row is an actual hole in the rack. -/
private theorem wire_launch_rack_empty (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ (layout storage I).wires) :
    ((layout storage I).rackX, e.source + (layout storage I).shift) ∉ (layout storage I).rack := by
  intro hp
  have hodd := (wires_launch storage I he).odd I
  simp only [Layout.rack, List.mem_toFinset, List.mem_append, List.mem_map, List.mem_flatMap] at hp
  rcases hp with ⟨y, hy, heq⟩ | ⟨g, hg, hp⟩
  · have heq := congrArg Prod.snd heq
    have hy := rackRows_even storage I hy
    dsimp at heq
    omega
  · have hne := (wires_launch storage I he).divider_neighbors storage I hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with heq | heq <;> have heq := congrArg Prod.snd heq <;> dsimp at heq <;> omega

private theorem blockers_row_empty (storage : Bool) (I : Instance) (row : ℕ)
    (hrow : row ∉ (layout storage I).dividers ++ (layout storage I).caps) :
    ((layout storage I).rackX - 1, row + (layout storage I).shift) ∉ (layout storage I).blockers := by
  intro hp
  obtain ⟨y, hy, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
  have he := congrArg Prod.snd he
  have hyrow : y = row := by dsimp at he; omega
  subst y
  exact hrow hy

private theorem register_row_even (r : Register) : r.row % 2 = 0 := by cases r <;> decide

namespace Stock

variable {I : Instance}

private theorem registerPoints_launch_empty (storage : Bool) (S : Stock I) {e : Wire}
    (he : e ∈ (layout storage I).wires) :
    ((layout storage I).rackX - 1, e.source + (layout storage I).shift) ∉ S.registerPoints storage := by
  intro hp
  obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hp
  have hy := congrArg Prod.snd heq
  dsimp at hy
  have hodd := (wires_launch storage I he).odd I
  have heven : (doorBase i.val + (S.register i).row) % 2 = 0 := by
    simp [doorBase, Nat.add_mod, Nat.mul_mod, register_row_even]
  omega

theorem launch_empty (storage : Bool) (S : Stock I) {e : Wire}
    (he : e ∈ (layout storage I).wires) :
    ((layout storage I).rackX - 1, e.source + (layout storage I).shift) ∉
      (layout storage I).fixed ∪ S.registerPoints storage := by
  intro hp
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · have hx := (layout storage I).pins_west hp
        dsimp at hx
        omega
      · have hx := (layout storage I).rack_column hp
        have hx := congrArg id hx
        dsimp at hx
        have hxpos : 0 < (layout storage I).rackX := by unfold Layout.rackX; omega
        omega
    · exact blockers_row_empty storage I e.source ((wires_launch storage I he).free storage I) hp
  · exact S.registerPoints_launch_empty storage he hp

theorem launch_support_empty (storage : Bool) (S : Stock I) {e : Wire}
    (he : e ∈ (layout storage I).wires) :
    ((layout storage I).rackX, e.source + (layout storage I).shift) ∉
      (layout storage I).fixed ∪ S.registerPoints storage := by
  intro hp
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · have hx := (layout storage I).pins_west hp
        dsimp at hx
        omega
      · exact wire_launch_rack_empty storage I he hp
    · have hx := (layout storage I).blockers_column hp
      have hxpos : 0 < (layout storage I).rackX := by unfold Layout.rackX; omega
      dsimp at hx
      omega
  · obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hp
    have hx := congrArg Prod.fst heq
    dsimp at hx
    have hxpos : 0 < (layout storage I).rackX := by unfold Layout.rackX; omega
    omega

theorem target_empty (storage : Bool) (S : Stock I) {e : Wire}
    (he : e ∈ (layout storage I).wires)
    (hregister : ((layout storage I).rackX - 1, e.target + (layout storage I).shift) ∉
      S.registerPoints storage) :
    ((layout storage I).rackX - 1, e.target + (layout storage I).shift) ∉
      (layout storage I).fixed ∪ S.registerPoints storage := by
  intro hp
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · have hx := (layout storage I).pins_west hp
        dsimp at hx
        omega
      · have hx := (layout storage I).rack_column hp
        dsimp at hx
        have hxpos : 0 < (layout storage I).rackX := by unfold Layout.rackX; omega
        omega
    · exact blockers_row_empty storage I e.target (wires_target_free storage I he) hp
  · exact hregister hp

/-- Away from pins, all stationary boxes lie in the two rack columns. -/
theorem private_clear (storage : Bool) (S : Stock I) {p : ℕ × ℕ}
    (hx : p.1 < (layout storage I).rackX - 1) (hpins : p ∉ (layout storage I).pins) :
    p ∉ (layout storage I).fixed ∪ S.registerPoints storage := by
  intro hp
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact hpins hp
      · have hc := (layout storage I).rack_column hp
        omega
    · have hc := (layout storage I).blockers_column hp
      omega
  · obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hp
    have hc := congrArg Prod.fst heq
    dsimp at hc
    omega

end Stock

end PushPuzzle.PushPush.Doors.Source
