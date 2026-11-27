/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptancePhysicalDynamics
public import Push.AcceptanceOrdinaryProbeReadout
public import PushS.PortCanonicalAccess
import all Push.AcceptanceGateRailTerminalPayments

/-! Actual ordinary target-axis probes and receiving-column payments exclude every lower endpoint fault. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram AcceptanceOrdinaryFailure

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) (hlegal : l.InputLegal target)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hlegal

/-- A target endpoint without its axis input has at least two actual terminal horizontal holes. -/
theorem canonical_endpoint_target_horizontal (e : Endpoint) (he : e ∈ l.endpoints)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (haxis : (if e.side = .upper then target.getD e.port false else !(target.getD e.port false)) = false)
    {horizontal : ℕ} (word : EndpointHorizontalReadout p e t horizontal) : 2 ≤ horizontal := by
  have receiving := l.canonical_endpoint_receiving target hlegal he haxis
  have hx0 := readLength_add_lt_x p e.port 0
  have hxW := x_add_readLength_lt_W p ((l.endpoints_port_lt hl he).trans_le haxes) 0
  have hyH := readDepth_add_lt_H p e.level
  let q : Cell (p.W + 1) (p.H + 1) :=
    (⟨if e.inward then p.x e.port + 2 else p.x e.port - 2, by split <;> omega⟩,
      ⟨if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level, by split <;> omega⟩)
  have ht := endpoint_second_target l p target e he receiving (q := q) rfl rfl
  have hdelta := endpoint_work_delta_of_target_second l p hl hM target e he (q := q) rfl rfl ht
  exact canonical_endpoint_horizontal_target_bound l p hl hM haxes initial target hgate e he hr accepted hdelta word

/-- The true shared ordinary axis word and its target probe exclude lower endpoint faults at the accepted endpoint. -/
theorem canonical_lower_endpoint_terminal_fault_impossible (e : Endpoint) (he : e ∈ l.endpoints)
    (hs : e.side = .lower) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : AxisInventories l p t) (fault : OrdinaryFaultReadout p e t) : False := by
  obtain ⟨upper, hu, hsu, hp⟩ := l.endpoints_upper_exists hl (l.endpoints_port_lt hl he)
  obtain ⟨a, word, _, _⟩ := canonical_ordinaryAxis_terminal_readout l p hl hM haxes initial target hgate
    hu he hsu hs hp.symm hr accepted (inventory.ordinary upper e hu he hsu hs hp.symm)
  have same := l.endpoint_axis_parameter_unique p hl hM haxes he fault.axis_word (word.lower_endpoint hs hp.symm)
  have failed := fault.axis_failed
  rw [same] at failed
  have hparameter : a.parameter ≤ 1 := by
    change 2 ≤ 3 - a.parameter at failed
    omega
  have htarget := (canonical_ordinary_target_threshold l p hl hM haxes initial target hgate hu he hsu hs hp.symm hr accepted word).mpr hparameter
  have haxis : (if e.side = .upper then target.getD e.port false else !(target.getD e.port false)) = false := by
    simp only [hs, reduceCtorEq, ite_false, ← hp, htarget, Bool.not_true]
  have supplied := canonical_endpoint_target_horizontal l p hl hM haxes initial target hgate hlegal e he hr accepted haxis fault.horizontal_word
  have bad := fault.horizontal_failed
  omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
