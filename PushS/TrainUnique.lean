/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.TrainDynamics

/-! Prescribed positive lengths and ordered occupied slots uniquely determine the three trains. -/

public section
namespace PushPuzzle.PushS.RowLabels.ThreeBlocks


private theorem eq_withStarts_of_slots (b : ThreeBlocks) (hpos : b.Positive) (hb : b.Separated)
    (first middle last : ℤ) (hc : (b.withStarts first middle last).Separated)
    (hslots : b.slots = (b.withStarts first middle last).slots) : b = b.withStarts first middle last := by
  let c := b.withStarts first middle last
  have hmem (i : Fin b.size) : b.point i ∈ c.slots := hslots ▸ b.point_mem i
  have he := Finset.orderEmbOfFin_unique (c.card_slots hc) hmem (b.strictMono_point hb)
  have hpoints : b.point = c.point := he.trans (c.orderEmbOfFin_eq_point hc)
  have h1 := hpos.1
  have h2 := hpos.2.1
  have h3 := hpos.2.2
  have hf : b.first = c.first := by
    have h := congrFun hpoints ⟨0, by dsimp only [size]; omega⟩
    have hB := b.point_first (j := 0) h1
    have hC := c.point_first (j := 0) h1
    simpa only [Int.natCast_zero, Int.add_zero] using hB.symm.trans (h.trans hC)
  have hm : b.middle = c.middle := by
    have h := congrFun hpoints ⟨b.firstLength, by dsimp only [size]; omega⟩
    have hB := b.point_middle (j := 0) h2
    have hC := c.point_middle (j := 0) h2
    simpa only [Nat.add_zero, Int.natCast_zero, Int.add_zero] using hB.symm.trans (h.trans hC)
  have hl : b.last = c.last := by
    have h := congrFun hpoints ⟨b.firstLength + b.middleLength, by dsimp only [size]; omega⟩
    have hB := b.point_last (j := 0) h3
    have hC := c.point_last (j := 0) h3
    simpa only [Nat.add_zero, Int.natCast_zero, Int.add_zero] using hB.symm.trans (h.trans hC)
  change b.first = first at hf
  change b.middle = middle at hm
  change b.last = last at hl
  cases b
  simp_all only [withStarts]

/-- Ordered trains of the same positive lengths with the same complete occupied slots have identical starts. -/
theorem eq_of_slots {b c : ThreeBlocks} (hpos : b.Positive) (hb : b.Separated) (hc : c.Separated)
    (hfirst : b.firstLength = c.firstLength) (hmiddle : b.middleLength = c.middleLength)
    (hlast : b.lastLength = c.lastLength) (hslots : b.slots = c.slots) : b = c := by
  have hshape : c = b.withStarts c.first c.middle c.last := by
    cases b
    cases c
    cases hfirst
    cases hmiddle
    cases hlast
    rfl
  rw [hshape] at hslots hc ⊢
  exact eq_withStarts_of_slots b hpos hb _ _ _ hc hslots

end PushPuzzle.PushS.RowLabels.ThreeBlocks
