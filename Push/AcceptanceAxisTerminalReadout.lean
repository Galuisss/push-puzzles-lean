/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisSeparated
public import Push.AcceptanceAxisTerminalReadoutGeometry
public import Push.AcceptanceAxisReadoutTrain

/-! Actual row clearing separates the three ordinary terminal trains and recovers their genuine words. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceAxisReadout

private theorem ordinary_slot_inside {p : Scales.Parameters} {upper lower : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {b : ThreeBlocks}
    (shape : OrdinaryAxisBlocks p upper lower u b) {y : ℤ} (hy : y ∈ b.slots) :
    0 < y ∧ y < p.H := by
  rw [← shape.slots] at hy
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
  have hR := (Finset.mem_filter.mp (Finset.mem_inter.mp hq).2).2
  exact ⟨by change (0 : ℤ) < q.2.val; omega, by change (q.2.val : ℤ) < p.H; omega⟩

private theorem ordinary_fits {p : Scales.Parameters} {upper lower : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {b : ThreeBlocks}
    (shape : OrdinaryAxisBlocks p upper lower u b) (positive : b.Positive) :
    1 ≤ b.first ∧ b.last + b.lastLength ≤ p.H := by
  have hf := ordinary_slot_inside shape ((b.mem_slots b.first).mpr
    (Or.inl ⟨le_rfl, by have h := positive.1; omega⟩))
  have hl := ordinary_slot_inside shape ((b.mem_slots (b.last + b.lastLength - 1)).mpr
    (Or.inr (Or.inr ⟨by have h := positive.2.2; omega, by omega⟩)))
  exact ⟨by omega, by omega⟩

private theorem ordinary_slot_of_box {p : Scales.Parameters} {upper lower : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {b : ThreeBlocks}
    (shape : OrdinaryAxisBlocks p upper lower u b) (q : Cell (p.W + 1) (p.H + 1))
    (hx : q.1.val = p.x upper.port) (hy : 0 < q.2.val ∧ q.2.val < p.H)
    (hq : q ∈ u.boxes) : (q.2.val : ℤ) ∈ b.slots := by
  rw [← shape.slots]
  exact Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr ⟨hq,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hy⟩⟩, rfl⟩

/-- The two internal gaps of an accepted terminal ordinary axis are positive. -/
private theorem canonical_ordinaryAxis_terminal_gapped (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {b : ThreeBlocks} (shape : OrdinaryAxisBlocks p upper lower t b) : b.Gapped := by
  have positive0 := l.ordinaryAxisTrainBlocks_positive p hl hM hu hlow (l.canonical initial)
  have positive : b.Positive := by
    change 0 < b.firstLength ∧ 0 < b.middleLength ∧ 0 < b.lastLength
    rw [shape.first_length, shape.middle_length, shape.last_length]
    exact positive0
  have hfit := ordinary_fits shape positive
  have hsep := shape.separated
  change b.first + b.firstLength ≤ b.middle ∧ b.middle + b.middleLength ≤ b.last at hsep
  have hfirst := shape.first_length
  have hmiddle := shape.middle_length
  have hlast := shape.last_length
  have hi := l.endpoints_port_lt hl hu
  have hxW := x_add_readLength_lt_W p (hi.trans_le haxes) 0
  have hH : p.H = 2 * p.D := rfl
  have hDu := readDepth_add_lt_D p upper.level
  have hDl := readDepth_add_lt_D p lower.level
  have hYu := l.endpoints_level_bounds p hl hM hu
  have hYl := l.endpoints_level_bounds p hl hM hlow
  have hru := readDepth_eq p hYu.1 hYu.2
  have hrl := readDepth_eq p hYl.1 hYl.2
  have hYu0 := p.Y_ge upper.level
  have hYl0 := p.Y_ge lower.level
  let top : Cell (p.W + 1) (p.H + 1) := (⟨p.x upper.port, by omega⟩, ⟨1, by omega⟩)
  let bottom : Cell (p.W + 1) (p.H + 1) := (⟨p.x upper.port, by omega⟩, ⟨p.H - 1, by omega⟩)
  have htop : top ∈ t.boxes := by
    have h := canonical_main_frame_neighbor_empty l p hl hM haxes initial target hr accepted hi top rfl (Or.inl rfl)
    simpa only [mem_holes, not_not] using h
  have hbottom : bottom ∈ t.boxes := by
    have h := canonical_main_frame_neighbor_empty l p hl hM haxes initial target hr accepted hi bottom rfl
      (Or.inr (by dsimp only [bottom]; omega))
    simpa only [mem_holes, not_not] using h
  have htopslot := ordinary_slot_of_box shape top rfl (by dsimp only [top]; omega) htop
  have hbottomslot := ordinary_slot_of_box shape bottom rfl (by dsimp only [bottom]; omega) hbottom
  have htbound := b.slots_bounds shape.separated htopslot
  have hbbound := b.slots_bounds shape.separated hbottomslot
  change b.first ≤ (1 : ℤ) ∧ (1 : ℤ) < b.last + b.lastLength at htbound
  change b.first ≤ ((p.H - 1 : ℕ) : ℤ) ∧ ((p.H - 1 : ℕ) : ℤ) < b.last + b.lastLength at hbbound
  have hfirstone : b.first = 1 := by omega
  have hlastend : b.last + b.lastLength = p.H := by omega
  let upperFour : Cell (p.W + 1) (p.H + 1) :=
    (⟨p.x upper.port, by omega⟩, ⟨p.Y upper.level + 4, by omega⟩)
  let lowerFour : Cell (p.W + 1) (p.H + 1) :=
    (⟨p.x upper.port, by omega⟩, ⟨p.H - (p.Y lower.level + 4), by omega⟩)
  have huFour := canonical_main_depth_four_occupied l p hl hM haxes initial target hr accepted
    hi hYu.1 hYu.2 .upper upperFour rfl rfl
  have hlFour := canonical_main_depth_four_occupied l p hl hM haxes initial target hr accepted
    hi hYl.1 hYl.2 .lower lowerFour rfl rfl
  have huSlot := ordinary_slot_of_box shape upperFour rfl (by dsimp only [upperFour]; omega) huFour
  have hlSlot := ordinary_slot_of_box shape lowerFour rfl (by dsimp only [lowerFour]; omega) hlFour
  rw [ThreeBlocks.mem_slots] at huSlot hlSlot
  dsimp only [upperFour, lowerFour] at huSlot hlSlot
  change b.first + b.firstLength < b.middle ∧ b.middle + b.middleLength < b.last
  constructor <;> omega

/-- Five actual terminal holes determine the genuine ordinary word, with both outer shifts zero. -/
theorem canonical_ordinaryAxis_terminal_readout (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : (holes t ∩ ordinaryAxis p upper.port).card = 5) :
    ∃ a, OrdinaryAxisReadout p upper lower t a ∧ a.upperShift = 0 ∧ a.lowerShift = 0 := by
  obtain ⟨b, shape⟩ := canonical_ordinaryAxis_blocks_of_terminal l p hl hM haxes initial target hgate
    hu hlow hsuSide hslSide hport hr .refl accepted inventory
  have gapped := canonical_ordinaryAxis_terminal_gapped l p hl hM haxes initial target hu hlow hr accepted shape
  have positive0 := l.ordinaryAxisTrainBlocks_positive p hl hM hu hlow (l.canonical initial)
  have positive : b.Positive := by
    change 0 < b.firstLength ∧ 0 < b.middleLength ∧ 0 < b.lastLength
    rw [shape.first_length, shape.middle_length, shape.last_length]
    exact positive0
  have word := ordinary_readout_of_shape (shape.toTrainShape gapped) positive
  refine ⟨ordinaryAxisPlacement p upper b, word, ?_, ?_⟩
  · exact canonical_endpoint_shift_zero l p hl hM haxes initial target hr accepted hu (word.upper_endpoint hsuSide)
  · exact canonical_endpoint_shift_zero l p hl hM haxes initial target hr accepted hlow
      (word.lower_endpoint hslSide hport)

/-- The first actual row clear restricts a genuine terminal ordinary parameter to one or two. -/
private theorem canonical_ordinaryAxis_terminal_parameter (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {a : OrdinaryAxisPlacement} (word : OrdinaryAxisReadout p upper lower t a)
    (hu0 : a.upperShift = 0) (hl0 : a.lowerShift = 0) : a.parameter = 1 ∨ a.parameter = 2 := by
  have hi := l.endpoints_port_lt hl hu
  have hxW := x_add_readLength_lt_W p (hi.trans_le haxes) 0
  have hH : p.H = 2 * p.D := rfl
  have hYu := l.endpoints_level_bounds p hl hM hu
  have hYl := l.endpoints_level_bounds p hl hM hlow
  have hDu := readDepth_add_lt_D p upper.level
  have hDl := readDepth_add_lt_D p lower.level
  have hru := readDepth_eq p hYu.1 hYu.2
  have hrl := readDepth_eq p hYl.1 hYl.2
  have hYu0 := p.Y_ge upper.level
  have hYl0 := p.Y_ge lower.level
  let upperThree : Cell (p.W + 1) (p.H + 1) :=
    (⟨p.x upper.port, by omega⟩, ⟨p.Y upper.level + 3, by omega⟩)
  let lowerThree : Cell (p.W + 1) (p.H + 1) :=
    (⟨p.x upper.port, by omega⟩, ⟨p.H - (p.Y lower.level + 3), by omega⟩)
  have huBox := canonical_main_depth_tail_occupied l p hl hM haxes initial target hr accepted
    hi hYu.1 hYu.2 .upper (Or.inl rfl) upperThree rfl rfl
  have hlBox := canonical_main_depth_tail_occupied l p hl hM haxes initial target hr accepted
    hi hYl.1 hYl.2 .lower (Or.inl rfl) lowerThree rfl rfl
  have hp := word.parameter_le
  have hzero : a.parameter ≠ 0 := by
    intro hzero
    have hhole : upperThree ∈ holes t := (word.upper_holes upperThree rfl
      (by dsimp only [upperThree]; omega)).mpr (Or.inr (by dsimp only [upperThree]; rw [hu0, hzero]; omega))
    exact (mem_holes upperThree).mp hhole huBox
  have hthree : a.parameter ≠ 3 := by
    intro hthree
    have hhole : lowerThree ∈ holes t := (word.lower_holes lowerThree rfl
      (by dsimp only [lowerThree]; omega)).mpr (Or.inr (by dsimp only [lowerThree]; rw [hl0, hthree]; omega))
    exact (mem_holes lowerThree).mp hhole hlBox
  omega

/-- A five-hole accepted terminal ordinary axis has a genuine binary endpoint word. -/
theorem canonical_ordinaryAxis_terminal_binary_readout (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : (holes t ∩ ordinaryAxis p upper.port).card = 5) :
    ∃ a, OrdinaryAxisReadout p upper lower t a ∧ a.upperShift = 0 ∧ a.lowerShift = 0 ∧
      (a.parameter = 1 ∨ a.parameter = 2) := by
  obtain ⟨a, word, hu0, hl0⟩ := canonical_ordinaryAxis_terminal_readout l p hl hM haxes initial target hgate
    hu hlow hsuSide hslSide hport hr accepted inventory
  exact ⟨a, word, hu0, hl0, canonical_ordinaryAxis_terminal_parameter l p hl hM haxes initial target
    hu hlow hr accepted word hu0 hl0⟩

end PushPuzzle.Push.AcceptanceSoundness
