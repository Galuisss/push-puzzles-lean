/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateRailTerminalPayments
public import Push.AcceptanceGateRailTrainMotion
import all PushS.PortGateIndexing
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality
import all PushS.PortSegments

/-! Actual accepted gate inventories recover genuine terminal rails, target threshold bits, and every prefix motion. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram

/-- A genuine physical gate rail together with the three target thresholds certified by its real samples. -/
structure GateRailTerminalReadout (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind)
    (t : State (p.W + 1) (p.H + 1)) (target : Shuttle.Target) (b : ThreeBlocks) : Prop where
  shape : GateTrainShape p g kind t b
  rail : GateRailReadout p g kind t (gateTrainPlacement p g b)
  heavy : target.heavy = true ↔ 6 ≤ (gateTrainPlacement p g b).short
  left : target.left = true ↔ (gateTrainPlacement p g b).left ≤ 1
  relay : target.relay = true ↔ (gateTrainPlacement p g b).right ≤ 1

private theorem rail_readout {p : Scales.Parameters} {g : Placement} {kind : Shuttle.Kind}
    {t : State (p.W + 1) (p.H + 1)} {b : ThreeBlocks} (shape : GateTrainShape p g kind t b)
    (hshape : g.right = g.left + 2) : GateRailReadout p g kind t (gateTrainPlacement p g b) := by
  have hgaps := shape.placement_gapped hshape
  refine ⟨shape.placement_ordered hshape, ?_, ?_, fun q hy hx => shape.core_hole hshape hy hx⟩
  · refine ⟨(gateTrainPlacement p g b).short, ?_⟩
    change ((gateTrainPlacement p g b).left : ℤ) - kind.kappa + 1 ≤ (gateTrainPlacement p g b).short ∧ _
    exact ⟨by omega, le_rfl⟩
  · refine ⟨(gateTrainPlacement p g b).short + 3, ?_⟩
    change _ ∧ (gateTrainPlacement p g b).short + 3 ≤ 13 - ((gateTrainPlacement p g b).right : ℤ)
    exact ⟨le_rfl, by omega⟩

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) (hlegal : l.InputLegal target)
  {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hlegal hg hk

/-- The actual eight samples and outer payments turn weak terminal blocks into the genuine target-threshold readout. -/
private theorem canonical_gateRail_readout_of_blocks {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {b : ThreeBlocks} (blocks : GateRailBlocks p g kind t b) :
    GateRailTerminalReadout p g kind t (canonicalShuttleTarget l target g) b := by
  obtain ⟨upper, hu, hsu, hp⟩ := l.endpoints_upper_exists hl (gate_middle_lt l hl (placement_gate_mem l hg hk))
  have samples := canonical_gate_shuttle_samples l p hl hM haxes initial target hgate hg hk hu hsu hp hr accepted blocks
  have legal := canonicalShuttleTarget_legal l target hlegal hg hk
  obtain ⟨left, right⟩ := canonical_gateRail_terminal_outer_payments l p hl hM haxes initial target hgate hg hk hr accepted blocks
  obtain ⟨gapped, heavy, leftBit, relay⟩ := blocks.gapped_of_samples (placement_gate_shape l hg hk).2
    (canonicalShuttleTarget l target g) legal samples left right
  have shape := blocks.toTrainShape gapped
  exact ⟨shape, rail_readout shape (placement_gate_shape l hg hk).2, heavy, leftBit, relay⟩

/-- Four middle-axis holes and κ+11 open-rail holes give the actual terminal gate's complete genuine readout. -/
theorem canonical_gateRail_terminal_readout {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    (railInventory : (holes t ∩ gateOpenRail p g).card = kind.kappa.toNat + 11) :
    ∃ b, GateRailTerminalReadout p g kind t (canonicalShuttleTarget l target g) b := by
  obtain ⟨b, blocks⟩ := canonical_gateRail_blocks_of_terminal l p hl hM haxes initial target hgate hg hk
    hr .refl accepted axisInventory railInventory
  exact ⟨b, canonical_gateRail_readout_of_blocks l p hl hM haxes initial target hgate hlegal hg hk hr accepted blocks⟩

/-- Those same actual terminal inventories recover the three genuine trains at every physical prefix. -/
theorem canonical_gateRail_shape_at {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    (railInventory : (holes t ∩ gateOpenRail p g).card = kind.kappa.toNat + 11) :
    ∃ b, GateTrainShape p g kind u b := by
  obtain ⟨terminal, readout⟩ := canonical_gateRail_terminal_readout l p hl hM haxes initial target hgate hlegal hg hk
    (hsu.trans hut) accepted axisInventory railInventory
  exact canonical_gateRail_shape_of_terminal_shape l p hl hM haxes initial target hgate hg hk hsu hut accepted
    axisInventory railInventory readout.shape

/-- Every true next move has the genuine three-train motion certified by the actual terminal gate inventories. -/
theorem canonical_gateRail_motion_of_terminal {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    (railInventory : (holes t ∩ gateOpenRail p g).card = kind.kappa.toNat + 11) :
    ∃ before after, GateTrainMotion p g kind u v before after := by
  obtain ⟨terminal, readout⟩ := canonical_gateRail_terminal_readout l p hl hM haxes initial target hgate hlegal hg hk
    ((hsu.tail step).trans hvt) accepted axisInventory railInventory
  exact canonical_gateRail_motion_of_terminal_shape l p hl hM haxes initial target hgate hg hk hsu step hvt accepted
    axisInventory railInventory readout.shape

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
