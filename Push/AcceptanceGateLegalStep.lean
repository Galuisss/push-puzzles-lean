/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisWithdrawal
public import PushS.PortGateGroupLegalStep
import all PushS.PortGateIndexing

/-! Actual gate first-failure classification from genuine shared-axis motion and the five physical fault exclusions. -/

public section
namespace PushPuzzle.Push.AcceptanceAxisReadout

open PushFS PushS PushS.PortLayout PushS.RowLabels

/-- Physical ordinary, relay, low-core and AND-left faults excluded at one actual gate state. -/
structure GateFaultExclusions (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind)
    (upper : Endpoint) (u : State (p.W + 1) (p.H + 1)) : Prop where
  left : ¬Nonempty (OrdinaryFaultReadout p ⟨g.side, g.left, true, g.level, g.internal⟩ u)
  right : ¬Nonempty (OrdinaryFaultReadout p ⟨g.side, g.right, false, g.level, g.internal + 2⟩ u)
  relay : ∀ blocks, GateRelayFault p g kind u blocks → False
  core : ∀ state, GateLowCoreFault p g kind upper u state → False
  andLeft : kind = .andGate → ∀ state, GateAndLeftFault p g upper u state → False

/-- A real shared-axis step preserves the full gate threshold when its actual physical faults are excluded. -/
theorem gate_group_legal_step_of_faults (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    {u v : State (p.W + 1) (p.H + 1)} (motions : AxisMotions l p u v)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)
    {before after : GateGroupPlacement} (source : GateGroupReadout p g kind upper u before)
    (target : GateGroupReadout p g kind upper v after)
    (beforeLegal : before.external.Legal kind) (excluded : GateFaultExclusions p g kind upper v)
    {d : Direction} (adjacent : Adjacent d u.player v.player) : after.external.Legal kind := by
  by_contra illegal
  have above := gate_group_loss_player_upper l p hl hM haxes motions hg hk hu hsu hp source target beforeLegal illegal adjacent
  have outsideRight : v.player ∉ gateRightGap p g (gateTrainPlacement p g after.core.rail) := by
    intro inside
    have below := gateRightGap_below_midline p g _ inside
    omega
  have outsideCore : v.player ∉ gateLowCorePrivate p g kind after.core := by
    intro inside
    have below := gateLowCorePrivate_below_midline p g kind after.core target.core.axis_readout.parameter_le inside
    omega
  have fault := Shuttle.fault_of_illegal kind (gateTrainPlacement p g after.core.rail) after.external illegal
  cases fault with
  | leftWire axis horizontal =>
    exact excluded.left ⟨⟨after.leftParameter, after.leftShift, (gateTrainPlacement p g after.core.rail).left,
      target.left_axis, axis, target.core.rail_shape.left_endpoint hl hg hk, horizontal⟩⟩
  | rightWire axis horizontal =>
    exact excluded.right ⟨⟨after.rightParameter, after.rightShift, (gateTrainPlacement p g after.core.rail).right,
      target.right_axis, axis, target.core.rail_shape.right_endpoint hl hg hk, horizontal⟩⟩
  | relay short right =>
    exact excluded.relay _ ⟨target.core.rail_shape, short, right, outsideRight⟩
  | orCore _ left short axis =>
    exact excluded.core _ ⟨target.core, short, axis, fun _ => left, outsideCore⟩
  | andCenter kind short axis =>
    subst kind
    exact excluded.core _ ⟨target.core, short, axis, (fun h => nomatch h), outsideCore⟩
  | andLeft kind short left =>
    subst kind
    have outsideLeft : v.player ∉ gateAndLeftPrivate p g after.core := by
      intro inside
      have below := gateAndLeftPrivate_below_midline p g after.core target.core.axis_readout.parameter_le inside
      omega
    exact excluded.andLeft rfl _ ⟨target.core, short, left, outsideLeft⟩

end PushPuzzle.Push.AcceptanceAxisReadout
