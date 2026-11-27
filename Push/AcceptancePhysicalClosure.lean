/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessProbeCancellation
public import Push.AcceptanceGlobalInventory

/-! Complete numerical and physical closure for an arbitrary accepted repaired source trajectory. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram AcceptanceAxisReadout

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) (hpartners : Partner.ReaderPartners l)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hpartners

/-- Every accepted repaired source has its full physical train dynamics, words and frozen endpoint boundaries. -/
theorem canonical_physical_dynamics (hlegal : l.InputLegal target)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    AcceptanceOrdinaryFailure.Dynamics l p (I).board (I).initial t := by
  have axes := canonical_axis_inventories l p hl hM haxes initial target hgate hpartners hr accepted
  have rails := canonical_gateRail_inventories_of_axes l p hl hM haxes initial target hgate hr accepted axes
  exact canonical_physical_dynamics_of_inventory l p hl hM haxes initial target hgate hlegal accepted axes rails

/-- Each actual accepted prefix has a complete original Boolean axis readout. -/
theorem canonical_axis_readout_exists {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    ∃ axes, l.AxisReadout p u axes :=
  canonical_axis_readout_exists_of_inventory l p hl hM haxes initial target hgate hsu hut accepted
    (canonical_axis_inventories l p hl hM haxes initial target hgate hpartners (hsu.trans hut) accepted)

/-- Every original gate rail in the arbitrary accepted endpoint has a genuine signed target readout. -/
theorem canonical_gateRail_terminal (hlegal : l.InputLegal target)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    ∃ blocks, GateRailTerminalReadout p g kind t (canonicalShuttleTarget l target g) blocks := by
  have axes := canonical_axis_inventories l p hl hM haxes initial target hgate hpartners hr accepted
  exact canonical_gateRail_terminal_readout l p hl hM haxes initial target hgate hlegal hg hk hr accepted
    (axes.gate g hg kind hk)
    (canonical_gateRail_holes_of_axes l p hl hM haxes initial target hgate hg hk hr accepted axes)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
