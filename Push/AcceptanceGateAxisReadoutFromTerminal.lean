/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateAxisTrainMotion
public import Push.AcceptanceGateAxisTerminalShape

/-! Genuine arbitrary terminal gate words supply all actual prefix words and shared two-train motions. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceAxisReadout

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) {g : Placement} (hg : g ∈ placements l)
  {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
  (hsuSide : upper.side = .upper) (hport : upper.port = g.left + 1)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hg hk hu hsuSide hport

/-- The complete terminal gate word restores the actual shared word at every accepted prefix. -/
theorem canonical_gateAxis_readout_of_terminal_word {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {terminal : GateAxisPlacement} (word : GateAxisReadout p g upper t terminal) :
    ∃ placement, GateAxisReadout p g upper u placement := by
  have depth := readDepth_ge p (l.endpoints_level_bounds p hl hM hu).1 (l.endpoints_level_bounds p hl hM hu).2
  have port : g.left + 1 < p.axes := by simpa only [hport] using (l.endpoints_port_lt hl hu).trans_le haxes
  have finalShape := gate_shape_of_readout word port (by omega)
  have inventory := gate_readout_card word port (by omega) hsuSide hport
  obtain ⟨blocks, shape⟩ := canonical_gateAxis_shape_of_terminal_shape l p hl hM haxes initial target hgate
    hg hk hu hsuSide hport hsu hut accepted inventory finalShape
  have positive : blocks.Positive := by
    change 0 < blocks.firstLength ∧ 0 < blocks.lastLength
    rw [shape.first_length, shape.last_length]
    exact l.gateAxisTrainBlocks_positive p hl hM hu (l.canonical initial)
  exact ⟨gateAxisPlacement p upper blocks, gate_readout_of_shape shape positive⟩

/-- The same arbitrary genuine terminal word determines every actual shared gate-axis step motion. -/
theorem canonical_gateAxis_motion_of_terminal_word {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {terminal : GateAxisPlacement} (word : GateAxisReadout p g upper t terminal) :
    ∃ before after, GateAxisTrainMotion p g upper u v before after := by
  have depth := readDepth_ge p (l.endpoints_level_bounds p hl hM hu).1 (l.endpoints_level_bounds p hl hM hu).2
  have port : g.left + 1 < p.axes := by simpa only [hport] using (l.endpoints_port_lt hl hu).trans_le haxes
  have finalShape := gate_shape_of_readout word port (by omega)
  have inventory := gate_readout_card word port (by omega) hsuSide hport
  exact canonical_gateAxis_motion_of_terminal_shape l p hl hM haxes initial target hgate
    hg hk hu hsuSide hport hsu step hvt accepted inventory finalShape

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
