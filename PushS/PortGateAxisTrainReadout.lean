/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateAxisTrainRigidity
import all PushS.PortLayoutCoordinates

/-! One parameter describes the upper ordinary pocket and the lower gate's middle-axis near holes. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- The ordinary-endpoint parameter and upper outer-rod shift of a gate's middle axis. -/
structure GateAxisPlacement where
  parameter : ℕ
  upperShift : ℕ

/-- Recover the shared parameter from the actual middle train start. -/
@[expose] def gateAxisPlacement (p : Scales.Parameters) (upper : Endpoint) (b : TwoBlocks) : GateAxisPlacement where
  parameter := ((readDepth p upper.level : ℤ) + 4 - b.last).toNat
  upperShift := (b.first - 1).toNat

/-- Actual upper half-axis holes and the lower gate-axis terminal gap. -/
structure GateAxisReadout (p : Scales.Parameters) (g : Placement) (upper : Endpoint)
    (u : State (p.W + 1) (p.H + 1)) (a : GateAxisPlacement) : Prop where
  parameter_le : a.parameter ≤ 3
  upper_budget : a.upperShift + a.parameter ≤ 3
  upper_holes (q : Cell (p.W + 1) (p.H + 1)) (axis : q.1.val = p.x (g.left + 1))
      (half : 0 < q.2.val ∧ q.2.val < p.D) :
    q ∈ holes u ↔ q.2.val ≤ a.upperShift ∨
      ((a.upperShift : ℤ) ≤ (q.2.val : ℤ) - readDepth p upper.level ∧
        (q.2.val : ℤ) - readDepth p upper.level ≤ 3 - (a.parameter : ℤ))
  core_holes (q : Cell (p.W + 1) (p.H + 1)) (axis : q.1.val = p.x (g.left + 1))
      (half : p.D ≤ q.2.val ∧ q.2.val < p.H - readDepth p 1) :
    q ∈ holes u ↔ p.H - readDepth p 1 - q.2.val ≤ a.parameter

namespace GateAxisTrainShape

variable {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
  {u : State (p.W + 1) (p.H + 1)} {b : TwoBlocks}

private theorem slot_inside (hs : GateAxisTrainShape p g upper u b) {y : ℤ} (hy : y ∈ b.slots) :
    0 < y ∧ y < p.H - readDepth p 1 := by
  rw [← hs.slots] at hy
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
  have hR := (Finset.mem_filter.mp (Finset.mem_inter.mp hq).2).2
  exact ⟨by change (0 : ℤ) < q.2.val; omega,
    by change (q.2.val : ℤ) < (p.H : ℤ) - readDepth p 1; have hD := readDepth_add_lt_H p 1; omega⟩

private theorem fits (hs : GateAxisTrainShape p g upper u b) (hpos : b.Positive) :
    1 ≤ b.first ∧ b.last + b.lastLength ≤ p.H - readDepth p 1 := by
  have hf := hs.slot_inside ((b.mem_slots b.first).mpr (Or.inl ⟨le_rfl, by have h := hpos.1; omega⟩))
  have hl := hs.slot_inside ((b.mem_slots (b.last + b.lastLength - 1)).mpr
    (Or.inr ⟨by have h := hpos.2; omega, by omega⟩))
  exact ⟨by omega, by omega⟩

private theorem placement_coordinates (hs : GateAxisTrainShape p g upper u b) (hpos : b.Positive) :
    let a := gateAxisPlacement p upper b
    (a.parameter : ℤ) = (readDepth p upper.level : ℤ) + 4 - b.last ∧ a.parameter ≤ 3 ∧
      (a.upperShift : ℤ) = b.first - 1 := by
  have hfit := hs.fits hpos
  have hgap := hs.gapped
  have hfirst := hs.first_length
  have hlast := hs.last_length
  have h1 := hpos.1
  have hDu := readDepth_add_lt_D p upper.level
  have hD1 := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  change b.first + b.firstLength < b.last at hgap
  have ht0 : 0 ≤ (readDepth p upper.level : ℤ) + 4 - b.last := by omega
  have ht3 : (readDepth p upper.level : ℤ) + 4 - b.last ≤ 3 := by omega
  have htcast := Int.toNat_of_nonneg ht0
  exact ⟨htcast, by change ((readDepth p upper.level : ℤ) + 4 - b.last).toNat ≤ 3; omega,
    Int.toNat_of_nonneg (by omega)⟩

private theorem box_iff (hs : GateAxisTrainShape p g upper u b)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ gateAxis p (g.left + 1)) :
    q ∈ u.boxes ↔ (q.2.val : ℤ) ∈ b.slots := by
  rw [← hs.slots]
  exact BoxMask.box_mem_iff_image (axis := .south) (lane := p.x (g.left + 1))
    (fun _ hr => (Finset.mem_filter.mp hr).2.1) u hq

private theorem readout (hs : GateAxisTrainShape p g upper u b) (hpos : b.Positive) :
    GateAxisReadout p g upper u (gateAxisPlacement p upper b) := by
  have hc := hs.placement_coordinates hpos
  have hgap := hs.gapped
  change b.first + b.firstLength < b.last at hgap
  have hfirst := hs.first_length
  have hlast := hs.last_length
  have h1 := hpos.1
  have hDu := readDepth_add_lt_D p upper.level
  have hD1 := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  refine ⟨hc.2.1, ?_, ?_, ?_⟩
  · omega
  · intro q hx hy
    have hR : q ∈ gateAxis p (g.left + 1) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hy.1, by omega⟩
    rw [mem_holes, hs.box_iff hR, TwoBlocks.mem_slots]
    omega
  · intro q hx hy
    have hR : q ∈ gateAxis p (g.left + 1) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, by omega, hy.2⟩
    rw [mem_holes, hs.box_iff hR, TwoBlocks.mem_slots]
    omega

end GateAxisTrainShape

/-- Every successful gate-axis prefix has the genuine ordinary endpoint parameter and the same core near-hole count. -/
theorem physicalInstance_gateAxis_train_readout (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    ∃ a, GateAxisReadout p g upper u a := by
  obtain ⟨b, hs⟩ := l.physicalInstance_gateAxis_train_shape p hl hM ha initial target hg hk hu hsuSide hp hsu hut ht
  have hpos0 := l.gateAxisTrainBlocks_positive p hl hM hu initial
  have hpos : b.Positive := by
    change 0 < b.firstLength ∧ 0 < b.lastLength
    rw [hs.first_length, hs.last_length]
    exact hpos0
  exact ⟨gateAxisPlacement p upper b, hs.readout hpos⟩

end PushPuzzle.PushS.PortLayout
