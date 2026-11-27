/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortLowerWithdrawal
public import PushS.PortGateCoreMotion
public import PushS.ShuttleFailure
import all PushS.PortGateIndexing

/-! All three actual gate inputs share the same physical joint gate readout. -/

public section
namespace PushPuzzle.PushS


/-- A monotone AND/OR input threshold can fail only by losing one of its three inputs. -/
theorem Shuttle.External.input_loss (kind : Shuttle.Kind) (before after : Shuttle.External)
    (hbefore : before.Legal kind) (hafter : ¬ after.Legal kind) :
    (before.left ≤ 1 ∧ 2 ≤ after.left) ∨ (2 ≤ before.middle ∧ after.middle ≤ 1) ∨
      (before.right ≤ 1 ∧ 2 ≤ after.right) := by
  cases kind <;> simp only [Shuttle.External.Legal] at hbefore hafter <;> omega

namespace PortLayout

open PushFS

/-- The joint actual gate state and the two outer ordinary half-axis words. -/
structure GateGroupPlacement where
  core : GateCorePlacement
  leftParameter : ℕ
  rightParameter : ℕ
  leftShift : ℕ
  rightShift : ℕ

/-- The three actual external thresholds supplied to the same AND/OR group. -/
@[expose] def GateGroupPlacement.external (state : GateGroupPlacement) : Shuttle.External :=
  ⟨state.leftParameter, state.core.axis.parameter, state.rightParameter⟩

/-- Complete genuine input and internal readouts of the same actual gate. -/
structure GateGroupReadout (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind) (upper : Endpoint)
    (u : State (p.W + 1) (p.H + 1)) (state : GateGroupPlacement) : Prop where
  core : GateCoreReadout p g kind upper u state.core
  left_axis : EndpointAxisReadout p ⟨g.side, g.left, true, g.level, g.internal⟩ u state.leftParameter state.leftShift
  right_axis : EndpointAxisReadout p ⟨g.side, g.right, false, g.level, g.internal + 2⟩ u state.rightParameter state.rightShift

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- Each actual successful gate prefix has all three external thresholds and both complete internal readouts. -/
theorem physicalInstance_gate_group_readout {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : ∃ state, GateGroupReadout p g kind upper u state := by
  obtain ⟨core, hc⟩ := l.physicalInstance_gate_core_readout p hl hM ha initial target hg hk hu hsuSide hp hsu hut ht
  have he := gate_endpoints l hg hk
  obtain ⟨left, ls, hlread⟩ := l.physicalInstance_endpoint_axis_readout p hl hM ha initial target _ he.1 hsu hut ht
  obtain ⟨right, rs, hrread⟩ := l.physicalInstance_endpoint_axis_readout p hl hM ha initial target _ he.2 hsu hut ht
  exact ⟨⟨core, left, right, ls, rs⟩, hc, hlread, hrread⟩

/-- The first actual failure of a lower gate's external threshold leaves its player in the upper half. -/
theorem physicalInstance_gate_group_loss_player_upper {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {before after : GateGroupPlacement} (hb : GateGroupReadout p g kind upper u before)
    (hc : GateGroupReadout p g kind upper v after)
    (hbefore : before.external.Legal kind) (hafter : ¬ after.external.Legal kind) : v.player.2.val < p.D := by
  have he := gate_endpoints l hg hk
  have hside := (placement_gate_shape l hg hk).1
  rcases Shuttle.External.input_loss kind before.external after.external hbefore hafter with hleft | hmid | hright
  · exact l.physicalInstance_lower_endpoint_loss_player_upper p hl hM ha initial target _ he.1 hside
      hsu hm hvt ht hb.left_axis hc.left_axis hleft.1 hleft.2
  · exact l.physicalInstance_gate_middle_loss_player_upper p hl hM ha initial target hg hk hu hsuSide hp
      hsu hm hvt ht hb.core.axis_readout hc.core.axis_readout hmid.1 hmid.2
  · exact l.physicalInstance_lower_endpoint_loss_player_upper p hl hM ha initial target _ he.2 hside
      hsu hm hvt ht hb.right_axis hc.right_axis hright.1 hright.2

end Solution
end PortLayout
end PushPuzzle.PushS
