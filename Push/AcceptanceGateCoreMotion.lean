/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceRailReadoutFailure
public import Push.AcceptanceDecodedInputsMotions
public import PushS.PortGateCoreMotion
import all PushS.PortGateIndexing

/-! Same-state and same-step gate core readouts from genuine horizontal and shared-axis motions. -/

public section
namespace PushPuzzle.Push.AcceptanceAxisReadout

open PushFS PushS PushS.PortLayout AcceptanceDecodedInputs

section Motion
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
  {B : Board (p.W + 1) (p.H + 1)} {u v : State (p.W + 1) (p.H + 1)}
  (axis : AxisMotions l p u v) (rails : RailMotions l p B u v)
  {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
  {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)

include axis rails hg hk hu hsu hp

/-- The true rail and shared-axis motions supply one joint core readout of the source state. -/
private theorem gate_core_readout_before : ∃ state, GateCoreReadout p g kind upper u state := by
  obtain ⟨before, _, rail⟩ := rails.gate g hg kind hk
  obtain ⟨beforeAxis, _, vertical⟩ := axis.gate g hg kind hk upper hu hsu hp
  exact ⟨⟨before, gateAxisPlacement p upper beforeAxis⟩, rail.before_shape,
    gate_readout_of_shape vertical.before_shape vertical.before_positive⟩

include hl hM haxes in
/-- One true step carries the same chosen core readout through its actual joint horizontal and vertical motions. -/
theorem gate_core_step_of_motions {before : GateCorePlacement} (readout : GateCoreReadout p g kind upper u before) :
    ∃ after, GateCoreStep p g kind upper u v before after := by
  obtain ⟨rb, ra, rail⟩ := rails.gate g hg kind hk
  have hrail := rail.before_shape.unique readout.rail_shape
  subst rb
  obtain ⟨vb, va, vertical⟩ := axis.gate g hg kind hk upper hu hsu hp
  have hbefore := gate_readout_of_shape vertical.before_shape vertical.before_positive
  have hafter := gate_readout_of_shape vertical.after_shape vertical.after_positive
  have hparam := l.endpoint_axis_parameter_unique p hl hM haxes hu
    (hbefore.upper_endpoint hsu hp) (readout.axis_readout.upper_endpoint hsu hp)
  refine ⟨⟨ra, gateAxisPlacement p upper va⟩, readout, ⟨rail.after_shape, hafter⟩, rail, ?_⟩
  intro outside
  have h := vertical.core_parameter_mono (by simpa only [hparam] using outside)
  simpa only [hparam] using h

include hl in
/-- The source state's actual joint gate core and both lower endpoint words assemble one full gate readout. -/
theorem gate_group_readout_before : ∃ state, GateGroupReadout p g kind upper u state := by
  obtain ⟨core, readout⟩ := gate_core_readout_before l p axis rails hg hk hu hsu hp
  have endpoints := gate_endpoints l hg hk
  have side := (placement_gate_shape l hg hk).1
  obtain ⟨left, ls, leftWord⟩ := axis.before_shared.lower_exists hl endpoints.1 side
  obtain ⟨right, rs, rightWord⟩ := axis.before_shared.lower_exists hl endpoints.2 side
  exact ⟨⟨core, left, right, ls, rs⟩, readout, leftWord, rightWord⟩

end Motion
end PushPuzzle.Push.AcceptanceAxisReadout
