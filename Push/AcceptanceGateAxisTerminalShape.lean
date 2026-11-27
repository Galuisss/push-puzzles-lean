/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisTerminalShape
public import Push.AcceptanceAxisReadoutGate

/-! The complete upper and lower-core gate words reconstruct the arbitrary gapped two-train terminal layout. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceAxisReadout

open PushFS PushS PushS.PortLayout PushS.RowLabels

/-- The actual two gate-axis train starts and fixed lengths determined by the complete shared word. -/
def gateReadoutBlocks (p : Scales.Parameters) (upper : Endpoint) (a : GateAxisPlacement) : TwoBlocks where
  first := 1 + a.upperShift
  last := (readDepth p upper.level : ℤ) + 4 - a.parameter
  firstLength := readDepth p upper.level - 1
  lastLength := p.H - readDepth p 1 - readDepth p upper.level - 4

/-- Genuine complete gate-axis words give the actual gapped layout at every allowed parameter and outer shift. -/
theorem gate_shape_of_readout {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {a : GateAxisPlacement}
    (word : GateAxisReadout p g upper u a) (hp : g.left + 1 < p.axes)
    (hY : 4 ≤ readDepth p upper.level) : GateAxisTrainShape p g upper u (gateReadoutBlocks p upper a) := by
  let b := gateReadoutBlocks p upper a
  have hDu := readDepth_add_lt_D p upper.level
  have hDl := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have budget := word.upper_budget
  have parameter := word.parameter_le
  have gapped : b.Gapped := by
    dsimp only [b, gateReadoutBlocks, TwoBlocks.Gapped]
    omega
  have boxWord (q : Cell (p.W + 1) (p.H + 1)) (hq : q ∈ gateAxis p (g.left + 1)) :
      q ∈ u.boxes ↔ (q.2.val : ℤ) ∈ b.slots := by
    obtain ⟨_, hx, hlo, hhi⟩ := Finset.mem_filter.mp hq
    have box : q ∈ u.boxes ↔ ¬q ∈ holes u := by simp only [mem_holes, not_not]
    rw [box, TwoBlocks.mem_slots]
    dsimp only [b, gateReadoutBlocks]
    by_cases above : q.2.val < p.D
    · rw [word.upper_holes q hx ⟨hlo, above⟩]
      omega
    · rw [word.core_holes q hx ⟨by omega, hhi⟩]
      omega
  refine ⟨rfl, rfl, gapped, ?_⟩
  apply Finset.ext
  intro y
  constructor
  · intro hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    exact (boxWord q (Finset.mem_inter.mp hq).2).mp (Finset.mem_inter.mp hq).1
  · intro hy
    have bounds := b.slots_bounds (le_of_lt gapped) hy
    have inside : 0 < y ∧ y < (p.H : ℤ) - readDepth p 1 := by
      dsimp only [b, gateReadoutBlocks] at bounds
      omega
    have hyval : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
    have hx := x_add_readLength_lt_W p hp 0
    let q : Cell (p.W + 1) (p.H + 1) := (⟨p.x (g.left + 1), by omega⟩, ⟨y.toNat, by omega⟩)
    have axis : q ∈ gateAxis p (g.left + 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, by dsimp only [q]; omega, by dsimp only [q]; omega⟩
    have occupied : q ∈ u.boxes := (boxWord q axis).mpr (by simpa only [q, hyval] using hy)
    exact Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr ⟨occupied, axis⟩, hyval⟩

/-- The complete genuine gate-axis word contains exactly the original four holes. -/
theorem gate_readout_card {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {a : GateAxisPlacement}
    (word : GateAxisReadout p g upper u a) (hp : g.left + 1 < p.axes)
    (hY : 4 ≤ readDepth p upper.level) (hsu : upper.side = .upper) (hport : upper.port = g.left + 1) :
    (holes u ∩ gateAxis p (g.left + 1)).card = 4 := by
  have hH : p.H = 2 * p.D := rfl
  have hD := readDepth_add_lt_D p 1
  have partition : holes u ∩ gateAxis p (g.left + 1) = halfHoles p upper u ∪ coreHoles p g u := by
    ext q
    have hq := q.2.isLt
    simp only [Finset.mem_inter, Finset.mem_union, halfHoles, coreHoles, gateAxis, Finset.mem_filter,
      Finset.mem_univ, true_and, hsu, hport, ite_true]
    constructor
    · rintro ⟨hole, hx, hy0, hyH⟩
      by_cases above : q.2.val < p.D
      · exact Or.inl ⟨hole, hx, hy0, above⟩
      · exact Or.inr ⟨hole, hx, by omega, hyH⟩
    · rintro (⟨hole, hx, hlo, hhi⟩ | ⟨hole, hx, hlo, hhi⟩) <;> exact ⟨hole, hx, by omega, by omega⟩
  have disjoint : Disjoint (halfHoles p upper u) (coreHoles p g u) := by
    apply Finset.disjoint_left.mpr
    intro q hu hc
    have upperDepth := (Finset.mem_filter.mp hu).2.2.2
    have coreDepth := (Finset.mem_filter.mp hc).2.2.1
    simp only [hsu, ite_true] at upperDepth
    omega
  have upperCard := endpoint_half_card (word.upper_endpoint hsu hport) (by simpa only [hport] using hp) hY
  rw [partition, Finset.card_union_of_disjoint disjoint, gate_core_card word hp]
  exact upperCard

end PushPuzzle.Push.AcceptanceAxisReadout
