/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortAxisTrainStep
public import PushS.PortGateAxisTrainStep
public import PushS.PortEndpointReadoutUnique
public import PushS.PortEndpointReadouts
import all PushS.PortGateAxisTrainReadout
import all PushS.PortLayoutCoordinates

/-! Withdrawing a lower-page axis input forces the actual player to the upper half of the board. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

private theorem target_y_le {p : Scales.Parameters} {d : Direction} {u v : State (p.W + 1) (p.H + 1)}
    (hadj : Adjacent d u.player v.player) : v.player.2.val ≤ u.player.2.val + 1 := by
  cases d <;> simp only [Adjacent] at hadj <;> omega

/-- Losing a lower ordinary input pushes from the upper end of the same actual middle train. -/
theorem OrdinaryAxisMotion.lower_loss_player_upper {p : Scales.Parameters} {upper lower : Endpoint}
    {u v : State (p.W + 1) (p.H + 1)} {before after : ThreeBlocks}
    (motion : OrdinaryAxisMotion p upper lower u v before after)
    (hbefore : (ordinaryAxisPlacement p upper before).lowerParameter ≤ 1)
    (hafter : 2 ≤ (ordinaryAxisPlacement p upper after).lowerParameter)
    {d : Direction} (hadj : Adjacent d u.player v.player) : v.player.2.val < p.D := by
  change 3 - ((readDepth p upper.level : ℤ) + 4 - before.middle).toNat ≤ 1 at hbefore
  change 2 ≤ 3 - ((readDepth p upper.level : ℤ) + 4 - after.middle).toNat at hafter
  have hm : before.middle < after.middle := by omega
  have hp := motion.middle_forward hm
  have hD := readDepth_add_lt_D p upper.level
  have hy := target_y_le hadj
  omega

/-- Losing the core's middle-axis input pushes from the upper end of that same actual middle train. -/
theorem GateAxisTrainMotion.lower_loss_player_upper {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
    {u v : State (p.W + 1) (p.H + 1)} {before after : TwoBlocks}
    (motion : GateAxisTrainMotion p g upper u v before after)
    (hbefore : 2 ≤ (gateAxisPlacement p upper before).parameter)
    (hafter : (gateAxisPlacement p upper after).parameter ≤ 1)
    {d : Direction} (hadj : Adjacent d u.player v.player) : v.player.2.val < p.D := by
  change 2 ≤ ((readDepth p upper.level : ℤ) + 4 - before.last).toNat at hbefore
  change ((readDepth p upper.level : ℤ) + 4 - after.last).toNat ≤ 1 at hafter
  have hm : before.last < after.last := by omega
  have hp := motion.last_forward hm
  have hD := readDepth_add_lt_D p upper.level
  have hy := target_y_le hadj
  omega

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- A genuine lower ordinary endpoint losing axis supply leaves the target player in the upper half. -/
theorem physicalInstance_lower_endpoint_loss_player_upper (e : Endpoint) (he : e ∈ l.endpoints) (hs : e.side = .lower)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {beforeParameter beforeShift afterParameter afterShift : ℕ}
    (hsource : EndpointAxisReadout p e u beforeParameter beforeShift)
    (htarget : EndpointAxisReadout p e v afterParameter afterShift)
    (hbefore : beforeParameter ≤ 1) (hafter : 2 ≤ afterParameter) : v.player.2.val < p.D := by
  obtain ⟨upper, hu, hsuSide, hp⟩ := l.endpoints_upper_exists hl (l.endpoints_port_lt hl he)
  obtain ⟨before, after, motion⟩ := l.physicalInstance_ordinaryAxis_train_motion p hl hM ha initial target
    hu he hsuSide hs hp.symm hsu hm hvt ht
  have hsrc := l.endpoint_axis_parameter_unique p hl hM ha he hsource (motion.before_readout.lower_endpoint hs hp.symm)
  have htgt := l.endpoint_axis_parameter_unique p hl hM ha he htarget (motion.after_readout.lower_endpoint hs hp.symm)
  exact motion.lower_loss_player_upper (by rwa [← hsrc]) (by rwa [← htgt]) (players_adjacent hm.choose_spec)

/-- A genuine lower core middle input losing supply leaves the target player in the upper half. -/
theorem physicalInstance_gate_middle_loss_player_upper {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {beforeAxis afterAxis : GateAxisPlacement} (hsource : GateAxisReadout p g upper u beforeAxis)
    (htarget : GateAxisReadout p g upper v afterAxis) (hbefore : 2 ≤ beforeAxis.parameter) (hafter : afterAxis.parameter ≤ 1) :
    v.player.2.val < p.D := by
  obtain ⟨before, after, motion⟩ := l.physicalInstance_gateAxis_train_motion p hl hM ha initial target
    hg hk hu hsuSide hp hsu hm hvt ht
  have hb := motion.before_shape.readout motion.before_positive
  have hc := motion.after_shape.readout motion.after_positive
  have hsrc := l.endpoint_axis_parameter_unique p hl hM ha hu (hsource.upper_endpoint hsuSide hp) (hb.upper_endpoint hsuSide hp)
  have htgt := l.endpoint_axis_parameter_unique p hl hM ha hu (htarget.upper_endpoint hsuSide hp) (hc.upper_endpoint hsuSide hp)
  exact motion.lower_loss_player_upper (by rwa [← hsrc]) (by rwa [← htgt]) (players_adjacent hm.choose_spec)

end Solution
end PushPuzzle.PushS.PortLayout
