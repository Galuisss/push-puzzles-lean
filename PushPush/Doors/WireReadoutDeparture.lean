/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutRows

/-! The first reverse-pin landing lies on an empty row away from its launch cap. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

/-- Empty even rows immediately outside a valid launch pair. -/
def DepartureGap (I : Instance) (row : ℕ) : Prop :=
  (∃ i < I.doors.length, ∃ a, 2 < a ∧ a + 2 < 90 ∧ a % 10 ≠ 0 ∧ row = doorBase i + a) ∨
    ∃ v j a, (a = 4 ∨ a = chamberHeight I - 4) ∧ row = roomBase I v j + a

private theorem DepartureGap.free {I : Instance} {row : ℕ} (h : DepartureGap I row)
    (storage : Bool) :
    row ∉ (layout storage I).dividers ++ (layout storage I).caps := by
  have hh := chamberHeight_ge I
  rcases h with ⟨i, hi, a, hlo, hhi, _, rfl⟩ | ⟨v, j, a, ha, rfl⟩
  · exact door_row_free storage I hi (by omega) (by omega)
  · apply room_row_free storage I v j <;> omega

private theorem DepartureGap.neighbors {I : Instance} {row : ℕ} (h : DepartureGap I row)
    (storage : Bool) {g : ℕ} (hg : g ∈ (layout storage I).dividers) :
    row ≠ g + 1 ∧ row + 1 ≠ g := by
  have hh := chamberHeight_ge I
  rcases h with ⟨i, hi, a, hlo, hhi, _, rfl⟩ | ⟨v, j, a, ha, rfl⟩
  · rcases mem_dividers storage I hg with ⟨k, hk, rfl⟩ | ⟨k, rfl⟩ <;>
      dsimp [doorBase] <;> omega
  · have hlo : 2 < a := by omega
    have hhi : a + 2 < chamberHeight I := by omega
    rcases mem_dividers storage I hg with ⟨i, hi, rfl⟩ | ⟨k, rfl⟩
    · dsimp [roomBase, doorBase]
      omega
    · constructor
      · intro he
        have hu := row_address_injective (by omega : a < chamberHeight I)
          (by omega : 1 < chamberHeight I) (show
            chamberHeight I * (slots I * v + j) + a = chamberHeight I * k + 1 by
              dsimp [roomBase] at he; omega)
        omega
      · intro he
        have hu := row_address_injective (by omega : a + 1 < chamberHeight I)
          (by omega : 0 < chamberHeight I) (show
            chamberHeight I * (slots I * v + j) + (a + 1) = chamberHeight I * k + 0 by
              dsimp [roomBase] at he; omega)
        omega

private theorem DepartureGap.register_empty {I : Instance} {row : ℕ} (h : DepartureGap I row)
    (door : Fin I.doors.length) (value : Register) : row ≠ doorBase door.val + value.row := by
  have hb := Register.row_bounds value
  have hm : value.row % 10 = 0 := by cases value <;> decide
  rcases h with ⟨i, hi, a, hlo, hhi, hmod, he⟩ | ⟨v, j, a, ha, he⟩
  · have ht : (doorBase door.val + value.row) % 10 = 0 := by
      unfold doorBase
      omega
    have hr : row % 10 ≠ 0 := by unfold doorBase at he; omega
    exact fun heq => hr (heq ▸ ht)
  · have hh := chamberHeight_ge I
    unfold roomBase doorBase at *
    omega

private theorem DepartureGap.rack_empty {I : Instance} {row : ℕ} (h : DepartureGap I row)
    (storage : Bool) : row ∉ (layout storage I).rackRows := by
  intro hr
  simp only [layout, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hr
  have hh := chamberHeight_ge I
  rcases h with ⟨i, hi, a, hlo, hhi, hmod, he⟩ | ⟨v, j, a, ha, he⟩
  · rcases hr with ⟨k, hk, b, hb, heq⟩ | ⟨k, hk, p, hp, heq⟩
    · have hm : b % 10 = 0 := by cases storage <;> simp at hb <;> omega
      have hrowmod : row % 10 ≠ 0 := by unfold doorBase at he; omega
      apply hrowmod
      rw [← heq]
      unfold doorBase
      omega
    · unfold doorBase at he
      omega
  · rcases hr with ⟨i, hi, b, hb, heq⟩ | ⟨k, hk, p, hp, heq⟩
    · have hblo : 0 < b ∧ b < 90 := by cases storage <;> simp at hb <;> omega
      unfold roomBase doorBase at *
      omega
    · have hpa : 10 + 8 * p < chamberHeight I := by unfold chamberHeight; omega
      have hu := row_address_injective (by omega : a < chamberHeight I) hpa
        (show chamberHeight I * (slots I * v + j) + a =
          chamberHeight I * k + (10 + 8 * p) by unfold roomBase at he; omega)
      unfold chamberHeight at hu ha
      omega

private theorem wires_departure_gap (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ (layout storage I).wires) :
    DepartureGap I (Layout.beside e.sourceSouth e.source) := by
  simp only [layout, wires, List.mem_append] at he
  rcases he with (((he | he) | he) | he) | he
  · obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
    have hi := List.mem_range.mp hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨i, hi, 38, by omega, by omega, by decide, by simp [Layout.beside, doorBase]⟩
    · exact Or.inl ⟨i, hi, 78, by omega, by omega, by decide, by simp [Layout.beside, doorBase]⟩
    · exact Or.inl ⟨i, hi, 52, by omega, by omega, by decide, by simp [Layout.beside, doorBase]⟩
    · exact Or.inl ⟨i, hi, 12, by omega, by omega, by decide, by simp [Layout.beside, doorBase]⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
    have hj := List.mem_range.mp hj
    cases hc : channelBit j
    · exact Or.inl ⟨j / 2, by omega, 62, by omega, by omega, by decide,
        by simp [arrivalWire, hc, Layout.beside, doorBase]⟩
    · exact Or.inl ⟨j / 2, by omega, 28, by omega, by omega, by decide,
        by simp [arrivalWire, hc, Layout.beside, doorBase]⟩
  · obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
    obtain ⟨j, _, he⟩ := List.mem_flatMap.mp he
    simp only [List.mem_ite_nil_right, List.mem_singleton] at he
    obtain ⟨_, rfl⟩ := he
    exact Or.inr ⟨v, j, 4, Or.inl rfl, by simp [Layout.beside, upperRow]⟩
  · obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
    obtain ⟨j, _, he⟩ := List.mem_flatMap.mp he
    simp only [List.mem_ite_nil_right, List.mem_singleton] at he
    obtain ⟨_, rfl⟩ := he
    have hh := chamberHeight_ge I
    exact Or.inr ⟨v, j, chamberHeight I - 4, Or.inr rfl,
      by simp only [Layout.beside, Bool.false_eq_true, ite_false, lowerRow]; omega⟩
  · cases storage
    · simp at he
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
      have hi := List.mem_range.mp hi
      by_cases hz : i = 0
      · exact Or.inr ⟨rank I I.target, 0, 4, Or.inl rfl,
          by simp [hz, Layout.beside, targetRow, upperRow]⟩
      · exact Or.inl ⟨i - 1, by omega, 68, by omega, by omega, by decide,
          by simp [hz, Layout.beside, doorBase]⟩

namespace Stock

variable {I : Instance}

private theorem departure_nonpin_empty (storage : Bool) (S : Stock I) {e : Wire}
    (he : e ∈ (layout storage I).wires) {p : ℕ × ℕ}
    (hy : p.2 = Layout.beside e.sourceSouth e.source + (layout storage I).shift) :
    p ∉ (layout storage I).rack ∪ (layout storage I).blockers ∪ S.registerPoints storage := by
  have hg := wires_departure_gap storage I he
  have hshift : 0 < (layout storage I).shift := by dsimp [Layout.shift]; omega
  intro hp
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · have hx := (layout storage I).rack_column hp
      have hp' : ((layout storage I).rackX, p.2) ∈ (layout storage I).rack := by
        simpa only [← hx] using hp
      rcases ((layout storage I).mem_rack_iff _).mp hp' with ⟨a, ha, hya⟩ | ⟨g, hdiv, hya | hya⟩
      · have heq : a = Layout.beside e.sourceSouth e.source := by omega
        exact hg.rack_empty storage (heq ▸ ha)
      · have hn := hg.neighbors storage hdiv
        omega
      · have hn := hg.neighbors storage hdiv
        omega
    · obtain ⟨a, ha, hpa⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
      have hya := congrArg Prod.snd hpa
      have heq : a = Layout.beside e.sourceSouth e.source := by dsimp at hya; omega
      exact hg.free storage (heq ▸ ha)
  · obtain ⟨i, _, hpi⟩ := Finset.mem_image.mp hp
    have hya := congrArg Prod.snd hpi
    exact hg.register_empty i (S.register i) (by dsimp at hya; omega)

/-- The row in which the first distant pin lands is completely empty in the
original stock, including every other wire's private pins. -/
theorem departure_row_empty (storage : Bool) (S : Stock I) {e : Wire}
    (he : e ∈ (layout storage I).wires)
    (hsignal : S.signal.2 = e.source + (layout storage I).shift) {p : ℕ × ℕ}
    (hy : p.2 = Layout.beside e.sourceSouth (e.source + (layout storage I).shift)) :
    p ∉ S.rawBoxes storage := by
  have hodd := (wires_launch storage I he).odd I
  have hpos : 0 < e.source := by omega
  have hfit := (wires_fit storage I he).1
  have hadd := beside_add e.sourceSouth e.source (layout storage I).shift hpos
  have hy' : p.2 = Layout.beside e.sourceSouth e.source + (layout storage I).shift := hy.trans hadd
  have heven : Layout.beside e.sourceSouth e.source % 2 = 0 := by
    cases e.sourceSouth <;> dsimp [Layout.beside] <;> omega
  have hband : (layout storage I).shift ≤ p.2 + 1 ∧
      p.2 ≤ (layout storage I).depth + (layout storage I).shift + 1 := by
    cases hs : e.sourceSouth <;> simp only [Layout.beside, hs, Bool.false_eq_true,
      ite_false, ite_true] at hy' <;> omega
  have hpin : p ∉ (layout storage I).pins := by
    intro hp
    rcases pins_row_cases storage I hp with hout | ⟨f, hf, hyr | hyr⟩
    · omega
    · have hfodd := (wires_launch storage I hf).odd I
      omega
    · have hfodd := (wires_terminalPin storage I hf).odd I
      change pinRow f % 2 = 1 at hfodd
      omega
  have hnonpin := S.departure_nonpin_empty storage he hy'
  intro hp
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_union.mp hp with hp | hp
        · exact hpin hp
        · exact hnonpin (Finset.mem_union_left _ (Finset.mem_union_left _ hp))
      · exact hnonpin (Finset.mem_union_left _ (Finset.mem_union_right _ hp))
    · exact hnonpin (Finset.mem_union_right _ hp)
  · have hp := congrArg Prod.snd (Finset.mem_singleton.mp hp)
    cases hs : e.sourceSouth <;> simp only [Layout.beside, hs, Bool.false_eq_true,
      ite_false, ite_true] at hy <;> omega

end Stock
end PushPuzzle.PushPush.Doors.Source
