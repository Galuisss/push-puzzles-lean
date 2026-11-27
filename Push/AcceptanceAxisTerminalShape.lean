/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisTrainMotion
public import Push.AcceptanceAxisReadoutHalfCard

/-! Arbitrary complementary endpoint words reconstruct the true gapped three-train terminal layout. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceAxisReadout

open PushFS PushS PushS.PortLayout PushS.RowLabels

/-- The three actual train starts and fixed lengths determined by the complete endpoint words. -/
def ordinaryReadoutBlocks (p : Scales.Parameters) (upper lower : Endpoint) (a : OrdinaryAxisPlacement) : ThreeBlocks where
  first := 1 + a.upperShift
  middle := (readDepth p upper.level : ℤ) + 4 - a.parameter
  last := (p.H : ℤ) - readDepth p lower.level + 1 - a.lowerShift
  firstLength := readDepth p upper.level - 1
  middleLength := p.H - readDepth p upper.level - readDepth p lower.level - 4
  lastLength := readDepth p lower.level - 1

/-- Genuine complementary half-axis words and the occupied central cut give the complete actual rigid layout. -/
theorem ordinary_shape_of_readout {p : Scales.Parameters} {upper lower : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {a : OrdinaryAxisPlacement}
    (word : OrdinaryAxisReadout p upper lower u a) (hp : upper.port < p.axes)
    (hYu : 4 ≤ readDepth p upper.level) (hYl : 4 ≤ readDepth p lower.level)
    (cut : ∀ q : Cell (p.W + 1) (p.H + 1), q.1.val = p.x upper.port → q.2.val = p.D → q ∉ holes u) :
    OrdinaryAxisTrainShape p upper lower u (ordinaryReadoutBlocks p upper lower a) := by
  let b := ordinaryReadoutBlocks p upper lower a
  have hDu := readDepth_add_lt_D p upper.level
  have hDl := readDepth_add_lt_D p lower.level
  have hH : p.H = 2 * p.D := rfl
  have upperBudget := word.upper_shift_le
  have lowerBudget := word.lower_shift_le
  have parameter := word.parameter_le
  have gapped : b.Gapped := by
    dsimp only [b, ordinaryReadoutBlocks, ThreeBlocks.Gapped]
    omega
  have boxWord (q : Cell (p.W + 1) (p.H + 1)) (hq : q ∈ ordinaryAxis p upper.port) :
      q ∈ u.boxes ↔ (q.2.val : ℤ) ∈ b.slots := by
    obtain ⟨_, hx, hlo, hhi⟩ := Finset.mem_filter.mp hq
    have box : q ∈ u.boxes ↔ ¬q ∈ holes u := by simp only [mem_holes, not_not]
    rw [box, ThreeBlocks.mem_slots]
    dsimp only [b, ordinaryReadoutBlocks]
    by_cases above : q.2.val < p.D
    · rw [word.upper_holes q hx ⟨hlo, above⟩]
      omega
    · by_cases middle : q.2.val = p.D
      · have occupied := cut q hx middle
        simp only [occupied, not_false_eq_true, true_iff]
        omega
      · rw [word.lower_holes q hx (by omega)]
        omega
  refine ⟨rfl, rfl, rfl, gapped, ?_⟩
  apply Finset.ext
  intro y
  constructor
  · intro hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    exact (boxWord q (Finset.mem_inter.mp hq).2).mp (Finset.mem_inter.mp hq).1
  · intro hy
    have bounds := b.slots_bounds ⟨le_of_lt gapped.1, le_of_lt gapped.2⟩ hy
    have inside : 0 < y ∧ y < p.H := by
      dsimp only [b, ordinaryReadoutBlocks] at bounds
      omega
    have hyval : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
    have hx := x_add_readLength_lt_W p hp 0
    let q : Cell (p.W + 1) (p.H + 1) := (⟨p.x upper.port, by omega⟩, ⟨y.toNat, by omega⟩)
    have axis : q ∈ ordinaryAxis p upper.port :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, by dsimp only [q]; omega, by dsimp only [q]; omega⟩
    have occupied : q ∈ u.boxes := (boxWord q axis).mpr (by simpa only [q, hyval] using hy)
    exact Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr ⟨occupied, axis⟩, hyval⟩

/-- The two genuine complementary words contain exactly the original five ordinary-axis holes. -/
theorem ordinary_readout_card {p : Scales.Parameters} {upper lower : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {a : OrdinaryAxisPlacement}
    (word : OrdinaryAxisReadout p upper lower u a) (hp : upper.port < p.axes)
    (hYu : 4 ≤ readDepth p upper.level) (hYl : 4 ≤ readDepth p lower.level)
    (hsu : upper.side = .upper) (hsl : lower.side = .lower) (hport : lower.port = upper.port)
    (cut : ∀ q : Cell (p.W + 1) (p.H + 1), q.1.val = p.x upper.port → q.2.val = p.D → q ∉ holes u) :
    (holes u ∩ ordinaryAxis p upper.port).card = 5 := by
  have hH : p.H = 2 * p.D := rfl
  have hD := readDepth_add_lt_D p upper.level
  have partition : holes u ∩ ordinaryAxis p upper.port = halfHoles p upper u ∪ halfHoles p lower u := by
    ext q
    have hq := q.2.isLt
    simp only [Finset.mem_inter, Finset.mem_union, halfHoles, ordinaryAxis, Finset.mem_filter,
      Finset.mem_univ, true_and, hsu, hsl, hport, reduceCtorEq, ite_true, ite_false]
    constructor
    · rintro ⟨hole, hx, hy0, hyH⟩
      by_cases above : q.2.val < p.D
      · exact Or.inl ⟨hole, hx, by omega, above⟩
      · by_cases middle : q.2.val = p.D
        · exact False.elim (cut q hx middle hole)
        · exact Or.inr ⟨hole, hx, by omega, by omega⟩
    · rintro (⟨hole, hx, hlo, hhi⟩ | ⟨hole, hx, hlo, hhi⟩) <;> exact ⟨hole, hx, by omega, by omega⟩
  have disjoint : Disjoint (halfHoles p upper u) (halfHoles p lower u) := by
    apply Finset.disjoint_left.mpr
    intro q hu hl
    have upperDepth := (Finset.mem_filter.mp hu).2.2
    have lowerDepth := (Finset.mem_filter.mp hl).2.2
    simp only [hsu, hsl, reduceCtorEq, ite_true, ite_false] at upperDepth lowerDepth
    omega
  have upperCard := endpoint_half_card (word.upper_endpoint hsu) hp hYu
  have lowerCard := endpoint_half_card (word.lower_endpoint hsl hport) (by simpa only [hport] using hp) hYl
  rw [partition, Finset.card_union_of_disjoint disjoint]
  unfold OrdinaryAxisPlacement.lowerParameter at lowerCard
  have parameter := word.parameter_le
  omega

end PushPuzzle.Push.AcceptanceAxisReadout
