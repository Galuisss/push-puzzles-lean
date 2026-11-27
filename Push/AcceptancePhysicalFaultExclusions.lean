/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceTerminalAxisTargets
public import Push.AcceptancePhysicalClosure
public import Push.AcceptanceLowerEndpointFaults
public import Push.AcceptancePhysicalRailFaults
public import Push.AcceptanceGateLegalStep
import all PushS.PortGateIndexing

/-! The real scan cancels every axis error and excludes all ordinary and gate faults throughout its physical trajectory. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceAxisReadout AcceptanceOrdinaryFailure

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) (hpartners : Partner.ReaderPartners l) (hlegal : l.InputLegal target)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hpartners hlegal

/-- Every actual terminal ordinary endpoint is supplied by its target axis or its real receiving-column payment. -/
private theorem canonical_endpoint_terminal_fault_impossible (e : Endpoint) (he : e ∈ l.endpoints)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (fault : OrdinaryFaultReadout p e t) : False := by
  cases hs : e.side with
  | upper =>
    have threshold := canonical_upper_endpoint_target_threshold l p hl hM haxes initial target hgate hpartners
      e he hs hr accepted fault.axis_word
    have axisFailed := fault.axis_failed
    have bit : target.getD e.port false = false := by
      cases bit : target.getD e.port false
      · rfl
      · have supplied := threshold.mp bit
        omega
    have haxis : (if e.side = .upper then target.getD e.port false else !(target.getD e.port false)) = false := by
      simp only [hs, ite_true, bit]
    have supplied := canonical_endpoint_target_horizontal l p hl hM haxes initial target hgate hlegal e he hr accepted haxis fault.horizontal_word
    have bad := fault.horizontal_failed
    omega
  | lower =>
    exact canonical_lower_endpoint_terminal_fault_impossible l p hl hM haxes initial target hgate hlegal e he hs hr accepted
      (canonical_axis_inventories l p hl hM haxes initial target hgate hpartners hr accepted) fault

/-- No actual prefix of an accepted source run has an ordinary endpoint fault. -/
theorem canonical_endpoint_fault_impossible (e : Endpoint) (he : e ∈ l.endpoints)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (fault : OrdinaryFaultReadout p e u) : False := by
  have dynamics := canonical_physical_dynamics l p hl hM haxes initial target hgate hpartners hlegal (hsu.trans hut) accepted
  have terminal : ¬Nonempty (OrdinaryFaultReadout p e t) := by
    rintro ⟨hf⟩
    exact canonical_endpoint_terminal_fault_impossible l p hl hM haxes initial target hgate hpartners hlegal e he
      (hsu.trans hut) accepted hf
  exact dynamics.failure_absent hl hM haxes e he
    (AcceptanceOrdinaryFailure.canonical_initial_outside l p hl hM haxes initial target e) terminal hsu hut ⟨fault⟩

/-- A real accepted terminal gate has no low-core fault: its three target threshold bits satisfy the native gate condition. -/
private theorem canonical_gate_terminal_lowCore_impossible {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hs : upper.side = .upper) (hp : upper.port = g.left + 1)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {state : GateCorePlacement} (fault : GateLowCoreFault p g kind upper t state) : False := by
  have axes := canonical_axis_inventories l p hl hM haxes initial target hgate hpartners hr accepted
  have rails := canonical_gateRail_inventories_of_axes l p hl hM haxes initial target hgate hr accepted axes
  obtain ⟨b, readout⟩ := canonical_gateRail_terminal_readout l p hl hM haxes initial target hgate hlegal hg hk hr accepted
    (axes.gate g hg kind hk) (rails.gate g hg kind hk)
  have same := fault.readout.rail_shape.unique readout.shape
  have low : (gateTrainPlacement p g b).short ≤ 5 := same ▸ fault.short
  have heavy : (canonicalShuttleTarget l target g).heavy = false := by
    cases bit : (canonicalShuttleTarget l target g).heavy
    · rfl
    · have high := readout.heavy.mp bit
      omega
  have hread := l.canonical_gate_read target hg hk
  have right : target.getD g.right false = true := by
    simpa only [canonicalShuttleTarget, hread.2.1, Bool.not_eq_false_eq_eq_true] using heavy
  have middle := (canonical_gate_target_threshold_of_partners l p hl hM haxes initial target hgate hpartners
    hg hk hu hs hp hr accepted fault.readout.axis_readout).mpr fault.axis_low
  have inputs := hlegal.gate_inputs hg hk
  cases kind with
  | andGate =>
    simp only [ite_true, right, Bool.true_eq_false, false_or] at inputs
    exact Bool.noConfusion (middle.symm.trans inputs.2)
  | orGate =>
    have failed : 2 ≤ (gateTrainPlacement p g b).left := same ▸ fault.left_if_or rfl
    have left : (canonicalShuttleTarget l target g).left = false := by
      cases bit : (canonicalShuttleTarget l target g).left
      · rfl
      · have supplied := readout.left.mp bit
        omega
    have leftBit : target.getD g.left false = true := by
      simpa only [canonicalShuttleTarget, hread.1, Bool.not_eq_false_eq_eq_true] using left
    simp only [reduceCtorEq, ite_false, leftBit, middle, right, Bool.true_eq_false, or_self] at inputs

/-- Genuine actual suffix dynamics exclude low-core faults at every accepted prefix. -/
private theorem canonical_gate_lowCore_fault_impossible {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hs : upper.side = .upper) (hp : upper.port = g.left + 1)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {state : GateCorePlacement} (fault : GateLowCoreFault p g kind upper u state) : False := by
  have dynamics := canonical_physical_dynamics l p hl hM haxes initial target hgate hpartners hlegal (hsu.trans hut) accepted
  obtain ⟨after, terminal⟩ := canonical_gate_low_core_failure_suffix_of_dynamics l p hl hM haxes initial target hgate
    hg hk hu hs hp hsu hut accepted dynamics fault
  exact canonical_gate_terminal_lowCore_impossible l p hl hM haxes initial target hgate hpartners hlegal hg hk hu hs hp
    (hsu.trans hut) accepted terminal

/-- All five physical gate fault classes are absent on the same actual accepted trajectory. -/
theorem canonical_gate_fault_exclusions {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hs : upper.side = .upper) (hp : upper.port = g.left + 1)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    GateFaultExclusions p g kind upper u := by
  have axes := canonical_axis_inventories l p hl hM haxes initial target hgate hpartners (hsu.trans hut) accepted
  have rails := canonical_gateRail_inventories_of_axes l p hl hM haxes initial target hgate (hsu.trans hut) accepted axes
  have endpoints := gate_endpoints l hg hk
  constructor
  · rintro ⟨fault⟩
    exact canonical_endpoint_fault_impossible l p hl hM haxes initial target hgate hpartners hlegal _ endpoints.1 hsu hut accepted fault
  · rintro ⟨fault⟩
    exact canonical_endpoint_fault_impossible l p hl hM haxes initial target hgate hpartners hlegal _ endpoints.2 hsu hut accepted fault
  · intro b fault
    exact canonical_gate_relay_fault_impossible_of_inventory l p hl hM haxes initial target hgate hlegal hg hk hsu hut accepted axes rails fault
  · intro state fault
    exact canonical_gate_lowCore_fault_impossible l p hl hM haxes initial target hgate hpartners hlegal hg hk hu hs hp hsu hut accepted fault
  · rintro rfl state fault
    exact canonical_gate_andLeft_fault_impossible_of_inventory l p hl hM haxes initial target hgate hlegal hg hk hu hs hp hsu hut accepted axes rails fault

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
