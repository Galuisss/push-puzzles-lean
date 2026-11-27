/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireSourceClear
public import PushPush.Doors.StockGeometry

/-! Every original pin sees only itself and the signal on each of its two lines. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction)

private theorem TerminalPinRow.free (storage : Bool) (I : Instance) {row : ℕ}
    (hr : TerminalPinRow I row) :
    row ∉ (layout storage I).dividers ++ (layout storage I).caps := by
  have hh := chamberHeight_ge I
  rcases hr with ⟨i, hi, a, ha, rfl⟩ | ⟨v, j, p, hp, rfl⟩
  · apply door_row_free storage I hi <;> simp only [DoorPinOffset] at ha <;> omega
  · have he : inputRow I v j p + 1 = roomBase I v j + (11 + 8 * p) := by unfold inputRow; omega
    rw [he]
    exact room_row_free storage I v j (by omega : 2 < 11 + 8 * p) (by unfold chamberHeight; omega)

theorem TerminalPinRow.divider_neighbors (storage : Bool) (I : Instance) {row g : ℕ}
    (hr : TerminalPinRow I row) (hg : g ∈ (layout storage I).dividers) :
    row ≠ g + 1 ∧ row + 1 ≠ g := by
  have hh := chamberHeight_ge I
  rcases hr with ⟨i, hi, a, ha, rfl⟩ | ⟨v, j, p, hp, he⟩
  · simp only [DoorPinOffset] at ha
    rcases mem_dividers storage I hg with ⟨k, hk, rfl⟩ | ⟨k, rfl⟩ <;>
      dsimp [doorBase] <;> omega
  · have he' : row = roomBase I v j + (11 + 8 * p) := by unfold inputRow at he; omega
    rw [he']
    rcases mem_dividers storage I hg with ⟨i, hi, rfl⟩ | ⟨k, rfl⟩
    · unfold roomBase doorBase
      omega
    · constructor
      · intro heq
        have hu := row_address_injective
          (by unfold chamberHeight; omega : 11 + 8 * p < chamberHeight I)
          (by omega : 1 < chamberHeight I)
          (show chamberHeight I * (slots I * v + j) + (11 + 8 * p) =
            chamberHeight I * k + 1 by unfold roomBase at heq; omega)
        omega
      · intro heq
        have hu := row_address_injective
          (by unfold chamberHeight; omega : 12 + 8 * p < chamberHeight I)
          (by omega : 0 < chamberHeight I)
          (show chamberHeight I * (slots I * v + j) + (12 + 8 * p) =
            chamberHeight I * k + 0 by unfold roomBase at heq; omega)
        omega

namespace Stock

variable {I : Instance}

theorem nonpin_row_band (storage : Bool) (S : Stock I) {p : ℕ × ℕ}
    (hp : p ∈ (layout storage I).rack ∪ (layout storage I).blockers ∪ S.registerPoints storage) :
    (layout storage I).shift ≤ p.2 + 1 ∧
      p.2 ≤ (layout storage I).depth + (layout storage I).shift + 1 := by
  let L := layout storage I
  have hfit := layout_fits storage I
  change L.Fits at hfit
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · have hx := L.rack_column hp
      have hp' : (L.rackX, p.2) ∈ L.rack := by simpa only [← hx] using hp
      rcases (L.mem_rack_iff _).mp hp' with ⟨y, hy, he⟩ | ⟨g, hg, he | he⟩
      · have hf := hfit.rack y hy
        change L.shift ≤ p.2 + 1 ∧ p.2 ≤ L.depth + L.shift + 1
        omega
      · have hf := hfit.dividers g hg
        change L.shift ≤ p.2 + 1 ∧ p.2 ≤ L.depth + L.shift + 1
        omega
      · have hf := hfit.dividers g hg
        change L.shift ≤ p.2 + 1 ∧ p.2 ≤ L.depth + L.shift + 1
        omega
    · obtain ⟨g, hg, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
      have hy := congrArg Prod.snd he
      have hf : g ≤ L.depth := by
        rcases List.mem_append.mp hg with hg | hg
        · exact hfit.dividers g hg
        · exact hfit.caps g hg
      change L.shift ≤ p.2 + 1 ∧ p.2 ≤ L.depth + L.shift + 1
      change g + L.shift = p.2 at hy
      omega
  · obtain ⟨i, _, he⟩ := Finset.mem_image.mp hp
    have hy := congrArg Prod.snd he
    have hr := Register.row_bounds (S.register i)
    have hi := i.isLt
    have hdepth : 90 * I.doors.length ≤ L.depth := by dsimp [L, layout]; omega
    change L.shift ≤ p.2 + 1 ∧ p.2 ≤ L.depth + L.shift + 1
    change doorBase i.val + (S.register i).row + L.shift = p.2 at hy
    dsimp [doorBase] at hy
    omega

private theorem logical_odd_row_empty (storage : Bool) (S : Stock I) (row : ℕ)
    (hodd : row % 2 = 1)
    (hfree : row ∉ (layout storage I).dividers ++ (layout storage I).caps)
    (hneighbors : ∀ g ∈ (layout storage I).dividers, row ≠ g + 1 ∧ row + 1 ≠ g)
    {p : ℕ × ℕ} (hrow : p.2 = row + (layout storage I).shift) :
    p ∉ (layout storage I).rack ∪ (layout storage I).blockers ∪ S.registerPoints storage := by
  intro hp
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · have hx := (layout storage I).rack_column hp
      have hp' : ((layout storage I).rackX, p.2) ∈ (layout storage I).rack := by
        simpa only [← hx] using hp
      rcases ((layout storage I).mem_rack_iff _).mp hp' with ⟨y, hy, he⟩ | ⟨g, hg, he | he⟩
      · have hy := rackRows_even storage I hy
        omega
      · have hn := hneighbors g hg
        omega
      · have hn := hneighbors g hg
        omega
    · obtain ⟨y, hy, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
      have hy' := congrArg Prod.snd he
      have heq : y = row := by dsimp at hy'; omega
      exact hfree (heq ▸ hy)
  · obtain ⟨i, _, he⟩ := Finset.mem_image.mp hp
    have hy := congrArg Prod.snd he
    dsimp at hy
    have hreven : (doorBase i.val + (S.register i).row) % 2 = 0 := by
      cases S.register i <;> simp [doorBase, Register.row, Nat.add_mod, Nat.mul_mod]
    omega

/-- No stationary non-pin box shares any original pin row. -/
theorem pin_row_nonpin_empty (storage : Bool) (S : Stock I) {pin p : ℕ × ℕ}
    (hpin : pin ∈ (layout storage I).pins) (hy : p.2 = pin.2) :
    p ∉ (layout storage I).rack ∪ (layout storage I).blockers ∪ S.registerPoints storage := by
  rcases pins_row_cases storage I hpin with hout | ⟨e, he, hr | hr⟩
  · intro hp
    have hb := S.nonpin_row_band storage hp
    omega
  · exact S.logical_odd_row_empty storage e.source ((wires_launch storage I he).odd I)
      ((wires_launch storage I he).free storage I)
      (fun g hg => (wires_launch storage I he).divider_neighbors storage I hg) (hy.trans hr)
  · exact S.logical_odd_row_empty storage (pinRow e) ((wires_terminalPin storage I he).odd I)
      ((wires_terminalPin storage I he).free storage I)
      (fun g hg => (wires_terminalPin storage I he).divider_neighbors storage I hg) (hy.trans hr)

theorem raw_row_at_pin (storage : Bool) (S : Stock I) {pin p : ℕ × ℕ}
    (hpin : pin ∈ (layout storage I).pins) (hy : p.2 = pin.2) :
    p ∈ S.rawBoxes storage ↔ p = pin ∨ p = S.signal := by
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_union.mp hp with hp | hp
        · rcases Finset.mem_union.mp hp with hp | hp
          · exact Or.inl (pins_same_row storage I hp hpin hy)
          · exact False.elim (S.pin_row_nonpin_empty storage hpin hy
              (Finset.mem_union_left _ (Finset.mem_union_left _ hp)))
        · exact False.elim (S.pin_row_nonpin_empty storage hpin hy
            (Finset.mem_union_left _ (Finset.mem_union_right _ hp)))
      · exact False.elim (S.pin_row_nonpin_empty storage hpin hy (Finset.mem_union_right _ hp))
    · exact Or.inr (Finset.mem_singleton.mp hp)
  · rintro (rfl | rfl)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ hpin)))
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

end Stock
end PushPuzzle.PushPush.Doors.Source
