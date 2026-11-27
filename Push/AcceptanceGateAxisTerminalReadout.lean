/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateAxisSeparated
public import Push.AcceptanceAxisTerminalReadoutGeometry
public import Push.AcceptanceAxisReadoutTrain

/-! Actual first-row clearing separates the gate-axis terminal trains and recovers their genuine word. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceAxisReadout

private theorem gate_slot_inside {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {b : TwoBlocks}
    (shape : GateAxisBlocks p g upper u b) {y : ℤ} (hy : y ∈ b.slots) :
    0 < y ∧ y < p.H - readDepth p 1 := by
  rw [← shape.slots] at hy
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
  have hR := (Finset.mem_filter.mp (Finset.mem_inter.mp hq).2).2
  exact ⟨by change (0 : ℤ) < q.2.val; omega,
    by change (q.2.val : ℤ) < (p.H : ℤ) - readDepth p 1
       have hD := readDepth_add_lt_H p 1
       omega⟩

private theorem gate_fits {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {b : TwoBlocks}
    (shape : GateAxisBlocks p g upper u b) (positive : b.Positive) :
    1 ≤ b.first ∧ b.last + b.lastLength ≤ p.H - readDepth p 1 := by
  have hf := gate_slot_inside shape ((b.mem_slots b.first).mpr
    (Or.inl ⟨le_rfl, by have h := positive.1; omega⟩))
  have hl := gate_slot_inside shape ((b.mem_slots (b.last + b.lastLength - 1)).mpr
    (Or.inr ⟨by have h := positive.2; omega, by omega⟩))
  exact ⟨by omega, by omega⟩

private theorem gate_slot_of_box {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {b : TwoBlocks}
    (shape : GateAxisBlocks p g upper u b) (q : Cell (p.W + 1) (p.H + 1))
    (hx : q.1.val = p.x (g.left + 1)) (hy : 0 < q.2.val ∧ q.2.val < p.H - readDepth p 1)
    (hq : q ∈ u.boxes) : (q.2.val : ℤ) ∈ b.slots := by
  rw [← shape.slots]
  exact Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr ⟨hq,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hy⟩⟩, rfl⟩

-- The cast-normalized two-block arithmetic produces a deeper kernel proof term.
set_option maxRecDepth 2048 in
/-- The terminal gate-axis internal gap is positive after the actual first row clear. -/
private theorem canonical_gateAxis_terminal_gapped (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) {g : Placement} {upper : Endpoint}
    (hu : upper ∈ l.endpoints) (hp : upper.port = g.left + 1)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {b : TwoBlocks} (shape : GateAxisBlocks p g upper t b) : b.Gapped := by
  have positive0 := l.gateAxisTrainBlocks_positive p hl hM hu (l.canonical initial)
  have positive : b.Positive := by
    change 0 < b.firstLength ∧ 0 < b.lastLength
    rw [shape.first_length, shape.last_length]
    exact positive0
  have hfit := gate_fits shape positive
  have hsep := shape.separated
  change b.first + b.firstLength ≤ b.last at hsep
  have hfirst := shape.first_length
  have hlast := shape.last_length
  have hi := l.endpoints_port_lt hl hu
  have hxW := x_add_readLength_lt_W p (hi.trans_le haxes) 0
  have hH : p.H = 2 * p.D := rfl
  have hDu := readDepth_add_lt_D p upper.level
  have hD1 := readDepth_add_lt_D p 1
  have hYu := l.endpoints_level_bounds p hl hM hu
  have hru := readDepth_eq p hYu.1 hYu.2
  have hr1 := readDepth_eq p le_rfl p.levels_pos
  have hYu0 := p.Y_ge upper.level
  have hY10 := p.Y_ge 1
  let top : Cell (p.W + 1) (p.H + 1) := (⟨p.x upper.port, by omega⟩, ⟨1, by omega⟩)
  have htop : top ∈ t.boxes := by
    have h := canonical_main_frame_neighbor_empty l p hl hM haxes initial target hr accepted hi top rfl (Or.inl rfl)
    simpa only [mem_holes, not_not] using h
  have htopslot := gate_slot_of_box shape top (by dsimp only [top]; rw [hp])
    (by dsimp only [top]; omega) htop
  have htbound := b.slots_bounds shape.separated htopslot
  change b.first ≤ (1 : ℤ) ∧ (1 : ℤ) < b.last + b.lastLength at htbound
  have hfirstone : b.first = 1 := by omega
  let lowerFour : Cell (p.W + 1) (p.H + 1) :=
    (⟨p.x upper.port, by omega⟩, ⟨p.H - (p.Y 1 + 4), by omega⟩)
  have hlFour := canonical_main_depth_four_occupied l p hl hM haxes initial target hr accepted
    hi le_rfl p.levels_pos .lower lowerFour rfl rfl
  have hlSlot := gate_slot_of_box shape lowerFour (by dsimp only [lowerFour]; rw [hp])
    (by dsimp only [lowerFour]; omega) hlFour
  rw [TwoBlocks.mem_slots] at hlSlot
  dsimp only [lowerFour] at hlSlot
  change b.first + b.firstLength < b.last
  omega

/-- Four actual terminal holes determine the genuine gate-axis word with zero upper outer shift. -/
theorem canonical_gateAxis_terminal_readout (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hs : upper.side = .upper) (hp : upper.port = g.left + 1)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4) :
    ∃ a, GateAxisReadout p g upper t a ∧ a.upperShift = 0 := by
  obtain ⟨b, shape⟩ := canonical_gateAxis_blocks_of_terminal l p hl hM haxes initial target hgate
    hg hk hu hs hp hr .refl accepted inventory
  have gapped := canonical_gateAxis_terminal_gapped l p hl hM haxes initial target hu hp hr accepted shape
  have positive0 := l.gateAxisTrainBlocks_positive p hl hM hu (l.canonical initial)
  have positive : b.Positive := by
    change 0 < b.firstLength ∧ 0 < b.lastLength
    rw [shape.first_length, shape.last_length]
    exact positive0
  have word := gate_readout_of_shape (shape.toTrainShape gapped) positive
  refine ⟨gateAxisPlacement p upper b, word, ?_⟩
  exact canonical_endpoint_shift_zero l p hl hM haxes initial target hr accepted hu
    (word.upper_endpoint hs hp)

end PushPuzzle.Push.AcceptanceSoundness
