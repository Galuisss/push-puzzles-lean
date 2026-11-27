/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessProbeCancellation
public import Push.AcceptanceGateProbeReadout
public import Push.AcceptanceOrdinaryProbeReadout
import all PushS.PortAxisGroups

/-! Actual cancelled probe observations identify every terminal upper-axis threshold with the original target bit. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) (hpartners : Partner.ReaderPartners l)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hpartners

/-- A genuine terminal gate-axis word reads its actual target bit after the real probe errors cancel. -/
theorem canonical_gate_target_threshold_of_partners {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hs : upper.side = .upper) (hp : upper.port = g.left + 1)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {a : GateAxisPlacement} (word : GateAxisReadout p g upper t a) :
    target.getD (g.left + 1) false = true ↔ a.parameter ≤ 1 := by
  let i : Fin l.portCount := ⟨upper.port, l.endpoints_port_lt hl hu⟩
  have observed := canonical_probe_observed_eq_target l p hl hM haxes initial target hgate hpartners hr accepted i
  have hthreshold := canonical_gate_target_threshold l p hl hM haxes initial target hg hk hu hs hp i rfl hr accepted word observed
  simpa only [i, hp] using hthreshold

/-- Every genuine terminal upper endpoint word has precisely the target's supplied-axis threshold. -/
theorem canonical_upper_endpoint_target_threshold (e : Endpoint) (he : e ∈ l.endpoints)
    (hs : e.side = .upper) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {parameter shift : ℕ} (word : EndpointAxisReadout p e t parameter shift) :
    target.getD e.port false = true ↔ parameter ≤ 1 := by
  have inventory := canonical_axis_inventories l p hl hM haxes initial target hgate hpartners hr accepted
  obtain ⟨groups⟩ := l.axisGroups_nonempty hl (l.endpoints_port_lt hl he)
  have ordinary (outer : e.port = groups.lower.left ∨ e.port = groups.lower.right) :
      target.getD e.port false = true ↔ parameter ≤ 1 := by
    obtain ⟨lower, hlow, hls, hlp, _⟩ := placement_outer_endpoint l groups.lower_mem outer
    have hlowSide := hls.trans groups.lower_side
    obtain ⟨a, joint, _, _⟩ := canonical_ordinaryAxis_terminal_readout l p hl hM haxes initial target hgate
      he hlow hs hlowSide hlp hr accepted (inventory.ordinary e lower he hlow hs hlowSide hlp)
    have same := l.endpoint_axis_parameter_unique p hl hM haxes he word (joint.upper_endpoint hs)
    rw [same]
    exact canonical_ordinary_target_threshold l p hl hM haxes initial target hgate he hlow hs hlowSide hlp hr accepted joint
  rcases groups.lower_port with left | right | ⟨gate, middle⟩
  · exact ordinary (Or.inl left)
  · exact ordinary (Or.inr right)
  · cases hk : groups.lower.gate with
    | none => simp only [hk, Option.isSome_none, Bool.false_eq_true] at gate
    | some kind =>
      obtain ⟨a, joint⟩ := canonical_gate_axis_readout_of_inventory l p hl hM haxes initial target hgate
        groups.lower_mem hk he hs middle hr .refl accepted inventory
      have same := l.endpoint_axis_parameter_unique p hl hM haxes he word (joint.upper_endpoint hs middle)
      rw [same, middle]
      exact canonical_gate_target_threshold_of_partners l p hl hM haxes initial target hgate hpartners
        groups.lower_mem hk he hs middle hr accepted joint

/-- The actual accepted terminal state has the complete original target Boolean axis readout. -/
theorem canonical_terminal_axis_readout (hlen : target.length = l.portCount)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    l.AxisReadout p t target := by
  have inventory := canonical_axis_inventories l p hl hM haxes initial target hgate hpartners hr accepted
  refine ⟨hlen, ?_, ?_⟩
  · intro e he _
    exact canonical_endpoint_axis_readout_of_inventory l p hl hM haxes initial target hgate e he hr .refl accepted inventory
  · intro e he hs parameter shift word
    exact canonical_upper_endpoint_target_threshold l p hl hM haxes initial target hgate hpartners e he hs hr accepted word

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
