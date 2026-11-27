/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireSourceRows
import Mathlib.Data.List.Nodup

/-! Uniqueness of source-generated wire endpoint rows. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors.Source

/-- Uniform junction addresses recover location, candidate, and local offset. -/
theorem room_row_injective (I : Instance) {v j v' j' a b : ℕ}
    (hj : j < slots I) (hj' : j' < slots I)
    (ha : a < chamberHeight I) (hb : b < chamberHeight I)
    (he : roomBase I v j + a = roomBase I v' j' + b) :
    v = v' ∧ j = j' ∧ a = b := by
  have hu := row_address_injective ha hb (show chamberHeight I * (slots I * v + j) + a =
      chamberHeight I * (slots I * v' + j') + b by unfold roomBase at he; omega)
  have hv := row_address_injective hj hj' hu.1
  exact ⟨hv.1, hv.2, hu.2⟩

private theorem nodup_flatMap_range {α : Type} (n : ℕ) (f : ℕ → List α)
    (hlocal : ∀ i < n, (f i).Nodup)
    (hindex : ∀ i < n, ∀ j < n, ∀ x ∈ f i, ∀ y ∈ f j, x = y → i = j) :
    ((List.range n).flatMap f).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun i hi => hlocal i (List.mem_range.mp hi), ?_⟩
  apply (List.nodup_range : (List.range n).Nodup).imp_of_mem
  intro i j hi hj hne
  apply List.disjoint_left.mpr
  intro x hx hy
  exact hne (hindex i (List.mem_range.mp hi) j (List.mem_range.mp hj) x hx x hy rfl)

private theorem internalWires_sources_nodup (I : Instance) :
    ((internalWires I).map Wire.source).Nodup := by
  simp only [internalWires, List.map_flatMap]
  apply nodup_flatMap_range
  · intro i _
    simp [List.nodup_cons]
  · intro i hi j hj x hx y hy he
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl <;> dsimp [doorBase] at he <;> omega

private theorem arrivalWires_sources_nodup (I : Instance) :
    ((arrivalWires I).map Wire.source).Nodup := by
  simp only [arrivalWires, List.map_map]
  apply List.Nodup.map_on _ List.nodup_range
  intro i hi j hj he
  dsimp [arrivalWire] at he
  have hbits : channelBit i = channelBit j := by
    cases hi' : channelBit i <;> cases hj' : channelBit j <;>
      simp_all [doorBase] <;> omega
  have hdiv : i / 2 = j / 2 := by
    rw [hbits] at he
    dsimp [doorBase] at he
    omega
  unfold channelBit at hbits
  have hm1 := Nat.mod_lt i (by decide : 0 < 2)
  have hm2 := Nat.mod_lt j (by decide : 0 < 2)
  by_cases hi' : i % 2 = 1 <;> by_cases hj' : j % 2 = 1 <;>
    simp [hi', hj'] at hbits <;> omega

private theorem choiceWires_sources_nodup (I : Instance) :
    ((choiceWires I).map Wire.source).Nodup := by
  simp only [choiceWires, List.map_flatMap]
  apply nodup_flatMap_range
  · intro v hv
    apply nodup_flatMap_range
    · intro j hj
      split <;> simp
    · intro j hj k hk x hx y hy he
      simp only [List.mem_map, List.mem_ite_nil_right, List.mem_singleton] at hx hy
      obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := hx
      obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := hy
      have hu := room_row_injective I (by unfold slots; omega : j < slots I)
        (by unfold slots; omega : k < slots I)
        (by have := chamberHeight_ge I; omega : 3 < chamberHeight I)
        (by have := chamberHeight_ge I; omega : 3 < chamberHeight I) he
      exact hu.2.1
  · intro v hv u hu x hx y hy he
    obtain ⟨j, hj, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨k, hk, hy⟩ := List.mem_flatMap.mp hy
    have hj := List.mem_range.mp hj
    have hk := List.mem_range.mp hk
    simp only [List.mem_map, List.mem_ite_nil_right, List.mem_singleton] at hx hy
    obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := hx
    obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := hy
    have hu := room_row_injective I (by unfold slots; omega : j < slots I)
      (by unfold slots; omega : k < slots I)
      (by have := chamberHeight_ge I; omega : 3 < chamberHeight I)
      (by have := chamberHeight_ge I; omega : 3 < chamberHeight I) he
    exact hu.1

private theorem skipWires_sources_nodup (I : Instance) :
    ((skipWires I).map Wire.source).Nodup := by
  have hh := chamberHeight_ge I
  simp only [skipWires, List.map_flatMap]
  apply nodup_flatMap_range
  · intro v hv
    apply nodup_flatMap_range
    · intro j hj
      split <;> simp
    · intro j hj k hk x hx y hy he
      simp only [List.mem_map, List.mem_ite_nil_right, List.mem_singleton] at hx hy
      obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := hx
      obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := hy
      have he' : roomBase I v j + (chamberHeight I - 3) =
          roomBase I v k + (chamberHeight I - 3) := by dsimp [lowerRow] at he; omega
      have hu := room_row_injective I (by unfold slots; omega : j < slots I)
        (by unfold slots; omega : k < slots I) (by omega) (by omega) he'
      exact hu.2.1
  · intro v hv u hu x hx y hy he
    obtain ⟨j, hj, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨k, hk, hy⟩ := List.mem_flatMap.mp hy
    have hj := List.mem_range.mp hj
    have hk := List.mem_range.mp hk
    simp only [List.mem_map, List.mem_ite_nil_right, List.mem_singleton] at hx hy
    obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := hx
    obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := hy
    have he' : roomBase I v j + (chamberHeight I - 3) =
        roomBase I u k + (chamberHeight I - 3) := by dsimp [lowerRow] at he; omega
    have hu := room_row_injective I (by unfold slots; omega : j < slots I)
      (by unfold slots; omega : k < slots I) (by omega) (by omega) he'
    exact hu.1

private theorem cleanupWires_sources_nodup (I : Instance) :
    ((cleanupWires I).map Wire.source).Nodup := by
  simp only [cleanupWires, List.map_map]
  apply List.Nodup.map_on _ List.nodup_range
  intro i hi j hj he
  have hi := List.mem_range.mp hi
  have hj := List.mem_range.mp hj
  dsimp at he
  by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
  · omega
  · simp only [ite_eq_left hi0, ite_eq_right hj0] at he
    have hb := targetRow_lower_bound I
    have hj' := door_row_before I (by omega : j - 1 < I.doors.length) (by omega : 69 < 90)
    omega
  · simp only [ite_eq_left hj0, ite_eq_right hi0] at he
    have hb := targetRow_lower_bound I
    have hi' := door_row_before I (by omega : i - 1 < I.doors.length) (by omega : 69 < 90)
    omega
  · simp only [ite_eq_right hi0, ite_eq_right hj0] at he
    dsimp [doorBase] at he
    omega

private theorem internal_source (I : Instance) {e : Wire} (he : e ∈ internalWires I) :
    ∃ i < I.doors.length, ∃ a ∈ ([11, 39, 51, 79] : List ℕ), e.source = doorBase i + a := by
  obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
  have hi := List.mem_range.mp hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    exact ⟨i, hi, _, by simp, rfl⟩

private theorem arrival_source (I : Instance) {e : Wire} (he : e ∈ arrivalWires I) :
    ∃ i < I.doors.length, ∃ a ∈ ([29, 61] : List ℕ), e.source = doorBase i + a := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
  have hj := List.mem_range.mp hj
  refine ⟨j / 2, by omega, _, ?_, rfl⟩
  cases channelBit j <;> simp

private theorem choice_source (I : Instance) {e : Wire} (he : e ∈ choiceWires I) :
    ∃ v j, j < slots I ∧ v ≠ rank I I.target ∧ e.source = upperRow I v j := by
  obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
  obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
  have hj := List.mem_range.mp hj
  simp only [List.mem_ite_nil_right, List.mem_singleton] at he
  obtain ⟨hcond, rfl⟩ := he
  exact ⟨v, j, by unfold slots; omega, hcond.1, rfl⟩

private theorem skip_source (I : Instance) {e : Wire} (he : e ∈ skipWires I) :
    ∃ v j, j < slots I ∧ e.source = lowerRow I v j := by
  obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
  obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
  have hj := List.mem_range.mp hj
  simp only [List.mem_ite_nil_right, List.mem_singleton] at he
  obtain ⟨_, rfl⟩ := he
  exact ⟨v, j, by unfold slots; omega, rfl⟩

private theorem cleanup_source (I : Instance) {e : Wire} (he : e ∈ cleanupWires I) :
    e.source = targetRow I ∨ ∃ i < I.doors.length, e.source = doorBase i + 69 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
  have hi := List.mem_range.mp hi
  by_cases hz : i = 0
  · exact Or.inl (by simp [hz])
  · exact Or.inr ⟨i - 1, by omega, by simp [hz]⟩

private theorem door_ne_room (I : Instance) {i a v j b : ℕ}
    (hi : i < I.doors.length) (ha : a < 90) : doorBase i + a ≠ roomBase I v j + b := by
  have hb := door_row_before I hi ha
  unfold roomBase
  omega

private theorem upper_ne_lower (I : Instance) {v j u k : ℕ} :
    upperRow I v j ≠ lowerRow I u k := by
  intro he
  have hh := chamberHeight_ge I
  have he' : chamberHeight I * (slots I * v + j) + 3 =
      chamberHeight I * (slots I * u + k) + (chamberHeight I - 3) := by
    unfold upperRow lowerRow roomBase at he
    omega
  have hu := row_address_injective (by omega : 3 < chamberHeight I)
    (by omega : chamberHeight I - 3 < chamberHeight I) he'
  omega

private theorem nodup_append_rows (row : Wire → ℕ) {left right : List Wire}
    (hl : (left.map row).Nodup) (hr : (right.map row).Nodup)
    (hne : ∀ e ∈ left, ∀ f ∈ right, row e ≠ row f) :
    ((left ++ right).map row).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨hl, hr, ?_⟩
  intro y hy y' hy' heq
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hy'
  exact hne e he f hf heq

/-- Every emitted wire has its own launch row, including storage cleanup. -/
theorem wires_sources_nodup (storage : Bool) (I : Instance) :
    (((layout storage I).wires).map Wire.source).Nodup := by
  have h01 := nodup_append_rows Wire.source (internalWires_sources_nodup I) (arrivalWires_sources_nodup I)
    (fun e he f hf heq => by
      obtain ⟨i, hi, a, ha, hrow⟩ := internal_source I he
      obtain ⟨j, hj, b, hb, hrow'⟩ := arrival_source I hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
      dsimp [doorBase] at hrow hrow'
      omega)
  have hdoor : ∀ e ∈ internalWires I ++ arrivalWires I,
      ∃ i < I.doors.length, ∃ a ∈ ([11, 29, 39, 51, 61, 79] : List ℕ),
        e.source = doorBase i + a := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨i, hi, a, ha, he⟩ := internal_source I he
      exact ⟨i, hi, a, by simp_all; omega, he⟩
    · obtain ⟨i, hi, a, ha, he⟩ := arrival_source I he
      exact ⟨i, hi, a, by simp_all; omega, he⟩
  have h012 := nodup_append_rows Wire.source h01 (choiceWires_sources_nodup I)
    (fun e he f hf heq => by
      obtain ⟨i, hi, a, ha, hr⟩ := hdoor e he
      obtain ⟨v, j, _, _, hr'⟩ := choice_source I hf
      have ha' : a < 90 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; omega
      exact door_ne_room I hi ha' (by simpa only [upperRow, hr, hr'] using heq))
  have h0123 := nodup_append_rows Wire.source h012 (skipWires_sources_nodup I)
    (fun e he f hf heq => by
      obtain ⟨u, k, _, hr'⟩ := skip_source I hf
      rcases List.mem_append.mp he with he | he
      · obtain ⟨i, hi, a, ha, hr⟩ := hdoor e he
        have ha' : a < 90 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; omega
        have hh := chamberHeight_ge I
        apply door_ne_room (v := u) (j := k) (b := chamberHeight I - 3) I hi ha'
        rw [hr, hr'] at heq
        unfold lowerRow at heq
        omega
      · obtain ⟨v, j, _, _, hr⟩ := choice_source I he
        exact upper_ne_lower I (hr ▸ hr' ▸ heq))
  have hclean : ∀ e ∈ internalWires I ++ arrivalWires I ++ choiceWires I ++ skipWires I,
      ∀ f ∈ cleanupWires I, e.source ≠ f.source := by
    intro e he f hf heq
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · obtain ⟨i, hi, a, ha, hr⟩ := hdoor e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases cleanup_source I hf with ht | ⟨j, hj, ht⟩
        · have hl := targetRow_lower_bound I
          have hb := door_row_before I hi (by omega : a < 90)
          omega
        · dsimp [doorBase] at hr ht
          omega
      · obtain ⟨v, j, hj, hv, hr⟩ := choice_source I he
        rcases cleanup_source I hf with ht | ⟨i, hi, ht⟩
        · have hu := room_row_injective I hj (slots_pos I)
            (by have := chamberHeight_ge I; omega : 3 < chamberHeight I)
            (by have := chamberHeight_ge I; omega : 3 < chamberHeight I)
            (show roomBase I v j + 3 = roomBase I (rank I I.target) 0 + 3 by
              rw [hr, ht] at heq; exact heq)
          exact hv hu.1
        · exact door_ne_room I hi (by omega : 69 < 90)
            (show doorBase i + 69 = roomBase I v j + 3 by rw [hr, ht] at heq; exact heq.symm)
    · obtain ⟨v, j, _, hr⟩ := skip_source I he
      rcases cleanup_source I hf with ht | ⟨i, hi, ht⟩
      · exact upper_ne_lower I (show upperRow I (rank I I.target) 0 = lowerRow I v j by
          rw [hr, ht] at heq; exact heq.symm)
      · have hh := chamberHeight_ge I
        apply door_ne_room (v := v) (j := j) (b := chamberHeight I - 3) I hi (by omega : 69 < 90)
        rw [hr, ht] at heq
        unfold lowerRow at heq
        omega
  cases storage
  · simpa only [layout, wires, Bool.false_eq_true, ite_false, List.append_nil] using h0123
  · simpa only [layout, wires, ite_true] using
      nodup_append_rows Wire.source h0123 (cleanupWires_sources_nodup I) hclean

/-- The final pin sits on the invalid-output side of its wired input. -/
def pinRow (e : Wire) : ℕ := Layout.beside e.targetSouth e.target

private theorem channel_address_injective {a b : ℕ} (ha : a < 90) (hb : b < 90) (hne : a ≠ b) :
    Function.Injective (fun j => doorBase (j / 2) + if channelBit j then a else b) := by
  intro i j he
  have hu := row_address_injective
    (by split <;> assumption : (if channelBit i then a else b) < 90)
    (by split <;> assumption : (if channelBit j then a else b) < 90)
    (show 90 * (i / 2) + (if channelBit i then a else b) =
      90 * (j / 2) + (if channelBit j then a else b) by exact he)
  have hbits : channelBit i = channelBit j := by
    cases hi : channelBit i <;> cases hj : channelBit j <;> simp_all
  unfold channelBit at hbits
  have hm1 := Nat.mod_lt i (by decide : 0 < 2)
  have hm2 := Nat.mod_lt j (by decide : 0 < 2)
  by_cases hi' : i % 2 = 1 <;> by_cases hj' : j % 2 = 1 <;>
    simp [hi', hj'] at hbits <;> omega

private theorem internalWires_pinRows_nodup (I : Instance) :
    ((internalWires I).map pinRow).Nodup := by
  simp only [internalWires, List.map_flatMap]
  apply nodup_flatMap_range
  · intro i _
    simp [pinRow, Layout.beside, List.nodup_cons]
  · intro i hi j hj x hx y hy he
    simp [pinRow, Layout.beside] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl <;> dsimp [doorBase] at he <;> omega

private theorem arrivalWires_pinRows_nodup (I : Instance) :
    ((arrivalWires I).map pinRow).Nodup := by
  simp only [arrivalWires, List.map_map]
  apply List.Nodup.map_on _ List.nodup_range
  intro i hi j hj he
  have hi := List.mem_range.mp hi
  have hj := List.mem_range.mp hj
  have he' : roomBase I (rank I (channel I i).target) 0 + (11 + 8 * i) =
      roomBase I (rank I (channel I j).target) 0 + (11 + 8 * j) := by
    dsimp [arrivalWire, pinRow, Layout.beside, inputRow] at he
    omega
  have hu := room_row_injective I (slots_pos I) (slots_pos I)
    (by unfold chamberHeight slots; omega : 11 + 8 * i < chamberHeight I)
    (by unfold chamberHeight slots; omega : 11 + 8 * j < chamberHeight I) he'
  omega

private theorem choice_pin_formula (I : Instance) (v j : ℕ) :
    pinRow (⟨upperRow I v j, true,
      doorBase (j / 2) + (if channelBit j then 50 else 40), !channelBit j⟩ : Wire) =
      doorBase (j / 2) + if channelBit j then 49 else 41 := by
  cases channelBit j <;> simp [pinRow, Layout.beside]

private theorem choiceWires_pinRows_nodup (I : Instance) : ((choiceWires I).map pinRow).Nodup := by
  simp only [choiceWires, List.map_flatMap]
  apply nodup_flatMap_range
  · intro v hv
    apply nodup_flatMap_range
    · intro j hj
      split <;> simp
    · intro j hj k hk x hx y hy he
      simp only [List.mem_map, List.mem_ite_nil_right, List.mem_singleton] at hx hy
      obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := hx
      obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := hy
      rw [choice_pin_formula, choice_pin_formula] at he
      exact channel_address_injective (by omega : 49 < 90) (by omega : 41 < 90) (by omega) he
  · intro v hv u hu x hx y hy he
    obtain ⟨j, _, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨k, _, hy⟩ := List.mem_flatMap.mp hy
    simp only [List.mem_map, List.mem_ite_nil_right, List.mem_singleton] at hx hy
    obtain ⟨_, ⟨hc, rfl⟩, rfl⟩ := hx
    obtain ⟨_, ⟨hc', rfl⟩, rfl⟩ := hy
    rw [choice_pin_formula, choice_pin_formula] at he
    have hjk := channel_address_injective (by omega : 49 < 90) (by omega : 41 < 90) (by omega) he
    subst k
    exact hc.2.symm.trans hc'.2

private theorem skipWires_pinRows_nodup (I : Instance) : ((skipWires I).map pinRow).Nodup := by
  have hh := chamberHeight_ge I
  simp only [skipWires, List.map_flatMap]
  apply nodup_flatMap_range
  · intro v hv
    apply nodup_flatMap_range
    · intro j hj
      split <;> simp
    · intro j hj k hk x hx y hy he
      simp only [List.mem_map, List.mem_ite_nil_right, List.mem_singleton] at hx hy
      obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := hx
      obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := hy
      have he' : roomBase I v (j + 1) + 11 = roomBase I v (k + 1) + 11 := by
        dsimp [pinRow, Layout.beside, inputRow] at he
        omega
      have hu := room_row_injective I (by unfold slots; omega : j + 1 < slots I)
        (by unfold slots; omega : k + 1 < slots I) (by omega) (by omega) he'
      omega
  · intro v hv u hu x hx y hy he
    obtain ⟨j, hj, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨k, hk, hy⟩ := List.mem_flatMap.mp hy
    have hj := List.mem_range.mp hj
    have hk := List.mem_range.mp hk
    simp only [List.mem_map, List.mem_ite_nil_right, List.mem_singleton] at hx hy
    obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := hx
    obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := hy
    have he' : roomBase I v (j + 1) + 11 = roomBase I u (k + 1) + 11 := by
      dsimp [pinRow, Layout.beside, inputRow] at he
      omega
    have hu := room_row_injective I (by unfold slots; omega : j + 1 < slots I)
      (by unfold slots; omega : k + 1 < slots I) (by omega) (by omega) he'
    exact hu.1

private theorem cleanupWires_pinRows_nodup (I : Instance) :
    ((cleanupWires I).map pinRow).Nodup := by
  simp only [cleanupWires, List.map_map]
  apply List.Nodup.map_on _ List.nodup_range
  intro i hi j hj he
  dsimp [pinRow, Layout.beside, doorBase] at he
  omega

private theorem internal_pin (I : Instance) {e : Wire} (he : e ∈ internalWires I) :
    ∃ i < I.doors.length, ∃ a ∈ ([9, 31, 59, 81] : List ℕ), pinRow e = doorBase i + a := by
  obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
  have hi := List.mem_range.mp hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨i, hi, 81, by simp, by simp [pinRow, Layout.beside]⟩
  · exact ⟨i, hi, 59, by simp, by simp [pinRow, Layout.beside]⟩
  · exact ⟨i, hi, 9, by simp, by simp [pinRow, Layout.beside]⟩
  · exact ⟨i, hi, 31, by simp, by simp [pinRow, Layout.beside]⟩

private theorem arrival_pin (I : Instance) {e : Wire} (he : e ∈ arrivalWires I) :
    ∃ v p, p < slots I ∧ pinRow e = roomBase I v 0 + (11 + 8 * p) := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
  have hj := List.mem_range.mp hj
  exact ⟨rank I (channel I j).target, j, by unfold slots; omega,
    by dsimp [arrivalWire, pinRow, Layout.beside, inputRow]; omega⟩

private theorem choice_pin (I : Instance) {e : Wire} (he : e ∈ choiceWires I) :
    ∃ i < I.doors.length, ∃ a ∈ ([41, 49] : List ℕ), pinRow e = doorBase i + a := by
  obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
  obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
  have hj := List.mem_range.mp hj
  simp only [List.mem_ite_nil_right, List.mem_singleton] at he
  obtain ⟨_, rfl⟩ := he
  refine ⟨j / 2, by omega, (if channelBit j then 49 else 41), ?_, choice_pin_formula I v j⟩
  cases channelBit j <;> simp

private theorem skip_pin (I : Instance) {e : Wire} (he : e ∈ skipWires I) :
    ∃ v j, 0 < j ∧ j < slots I ∧ pinRow e = roomBase I v j + 11 := by
  obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
  obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
  have hj := List.mem_range.mp hj
  simp only [List.mem_ite_nil_right, List.mem_singleton] at he
  obtain ⟨_, rfl⟩ := he
  exact ⟨v, j + 1, by omega, by unfold slots; omega,
    by simp [pinRow, Layout.beside, inputRow, Nat.add_assoc]⟩

private theorem cleanup_pin (I : Instance) {e : Wire} (he : e ∈ cleanupWires I) :
    ∃ i < I.doors.length, pinRow e = doorBase i + 71 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
  exact ⟨i, List.mem_range.mp hi, by simp [pinRow, Layout.beside]⟩

/-- Every wired input has its own terminal-pin row. -/
private theorem wires_pinRows_nodup (storage : Bool) (I : Instance) :
    (((layout storage I).wires).map pinRow).Nodup := by
  have hh := chamberHeight_ge I
  have h01 := nodup_append_rows pinRow (internalWires_pinRows_nodup I) (arrivalWires_pinRows_nodup I)
    (fun e he f hf heq => by
      obtain ⟨i, hi, a, ha, hr⟩ := internal_pin I he
      obtain ⟨v, p, hp, hr'⟩ := arrival_pin I hf
      have ha' : a < 90 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; omega
      exact door_ne_room I hi ha' (hr ▸ hr' ▸ heq))
  have h012 := nodup_append_rows pinRow h01 (choiceWires_pinRows_nodup I)
    (fun e he f hf heq => by
      obtain ⟨i, hi, a, ha, hr'⟩ := choice_pin I hf
      have ha' : a < 90 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; omega
      rcases List.mem_append.mp he with he | he
      · obtain ⟨j, hj, b, hb, hr⟩ := internal_pin I he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
        dsimp [doorBase] at hr hr'
        omega
      · obtain ⟨v, p, hp, hr⟩ := arrival_pin I he
        exact door_ne_room I hi ha' (show doorBase i + a = roomBase I v 0 + (11 + 8 * p) by
          rw [hr, hr'] at heq; exact heq.symm))
  have h0123 := nodup_append_rows pinRow h012 (skipWires_pinRows_nodup I)
    (fun e he f hf heq => by
      obtain ⟨v, j, hj0, hj, hr'⟩ := skip_pin I hf
      rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · obtain ⟨i, hi, a, ha, hr⟩ := internal_pin I he
          have ha' : a < 90 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; omega
          exact door_ne_room I hi ha' (hr ▸ hr' ▸ heq)
        · obtain ⟨u, p, hp, hr⟩ := arrival_pin I he
          have hu := room_row_injective I (slots_pos I) hj
            (by unfold chamberHeight; omega : 11 + 8 * p < chamberHeight I) (by omega : 11 < chamberHeight I)
            (hr ▸ hr' ▸ heq)
          omega
      · obtain ⟨i, hi, a, ha, hr⟩ := choice_pin I he
        have ha' : a < 90 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; omega
        exact door_ne_room I hi ha' (hr ▸ hr' ▸ heq))
  have hclean : ∀ e ∈ internalWires I ++ arrivalWires I ++ choiceWires I ++ skipWires I,
      ∀ f ∈ cleanupWires I, pinRow e ≠ pinRow f := by
    intro e he f hf heq
    obtain ⟨i, hi, hr'⟩ := cleanup_pin I hf
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · obtain ⟨j, hj, a, ha, hr⟩ := internal_pin I he
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          dsimp [doorBase] at hr hr'
          omega
        · obtain ⟨v, p, hp, hr⟩ := arrival_pin I he
          exact door_ne_room I hi (by omega : 71 < 90)
            (show doorBase i + 71 = roomBase I v 0 + (11 + 8 * p) by rw [hr, hr'] at heq; exact heq.symm)
      · obtain ⟨j, hj, a, ha, hr⟩ := choice_pin I he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        dsimp [doorBase] at hr hr'
        omega
    · obtain ⟨v, j, _, _, hr⟩ := skip_pin I he
      exact door_ne_room I hi (by omega : 71 < 90)
        (show doorBase i + 71 = roomBase I v j + 11 by rw [hr, hr'] at heq; exact heq.symm)
  cases storage
  · simpa only [layout, wires, Bool.false_eq_true, ite_false, List.append_nil] using h0123
  · simpa only [layout, wires, ite_true] using
      nodup_append_rows pinRow h0123 (cleanupWires_pinRows_nodup I) hclean

/-- A launch row identifies its actual emitted wire. -/
theorem wires_eq_of_source_eq (storage : Bool) (I : Instance) {e f : Wire}
    (he : e ∈ (layout storage I).wires) (hf : f ∈ (layout storage I).wires)
    (heq : e.source = f.source) : e = f :=
  List.inj_on_of_nodup_map (wires_sources_nodup storage I) he hf heq

/-- A terminal pin row identifies its actual emitted wire. -/
theorem wires_eq_of_pinRow_eq (storage : Bool) (I : Instance) {e f : Wire}
    (he : e ∈ (layout storage I).wires) (hf : f ∈ (layout storage I).wires)
    (heq : pinRow e = pinRow f) : e = f :=
  List.inj_on_of_nodup_map (wires_pinRows_nodup storage I) he hf heq

end PushPuzzle.PushPush.Doors.Source
