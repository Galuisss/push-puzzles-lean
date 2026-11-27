/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisReadoutTrain
public import PushS.PortGateGroupReadout
import all PushS.PortGateIndexing

/-! A first lower input loss forces the actual player to the upper page through genuine shared train motion. -/

public section
namespace PushPuzzle.Push.AcceptanceAxisReadout

open PushFS PushS PushS.PortLayout

section Motion
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
  {u v : State (p.W + 1) (p.H + 1)} (motions : AxisMotions l p u v)

include hl hM haxes motions

/-- An actual lower endpoint losing axis supply pushes from the upper end of its middle train. -/
private theorem lower_endpoint_loss_player_upper (e : Endpoint) (he : e ∈ l.endpoints)
    (hs : e.side = .lower)
    {beforeParameter beforeShift afterParameter afterShift : ℕ}
    (source : EndpointAxisReadout p e u beforeParameter beforeShift)
    (target : EndpointAxisReadout p e v afterParameter afterShift)
    (beforeSupplied : beforeParameter ≤ 1) (afterFailed : 2 ≤ afterParameter)
    {d : Direction} (adjacent : Adjacent d u.player v.player) : v.player.2.val < p.D := by
  obtain ⟨upper, hu, hsu, hp⟩ := l.endpoints_upper_exists hl (l.endpoints_port_lt hl he)
  obtain ⟨before, after, motion⟩ := motions.ordinary upper e hu he hsu hs hp.symm
  have hsrc := l.endpoint_axis_parameter_unique p hl hM haxes he source (motion.before_readout.lower_endpoint hs hp.symm)
  have htgt := l.endpoint_axis_parameter_unique p hl hM haxes he target (motion.after_readout.lower_endpoint hs hp.symm)
  exact motion.lower_loss_player_upper (by rwa [← hsrc]) (by rwa [← htgt]) adjacent

/-- Losing the actual lower gate middle supply pushes from that same shared train's upper end. -/
private theorem gate_middle_loss_player_upper {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)
    {beforeAxis afterAxis : GateAxisPlacement} (source : GateAxisReadout p g upper u beforeAxis)
    (target : GateAxisReadout p g upper v afterAxis)
    (beforeSupplied : 2 ≤ beforeAxis.parameter) (afterFailed : afterAxis.parameter ≤ 1)
    {d : Direction} (adjacent : Adjacent d u.player v.player) : v.player.2.val < p.D := by
  obtain ⟨before, after, motion⟩ := motions.gate g hg kind hk upper hu hsu hp
  have hb := gate_readout_of_shape motion.before_shape motion.before_positive
  have hc := gate_readout_of_shape motion.after_shape motion.after_positive
  have hsrc := l.endpoint_axis_parameter_unique p hl hM haxes hu (source.upper_endpoint hsu hp) (hb.upper_endpoint hsu hp)
  have htgt := l.endpoint_axis_parameter_unique p hl hM haxes hu (target.upper_endpoint hsu hp) (hc.upper_endpoint hsu hp)
  exact motion.lower_loss_player_upper (by rwa [← hsrc]) (by rwa [← htgt]) adjacent

/-- The first failure of an actual lower gate's complete external threshold leaves its player on the upper page. -/
theorem gate_group_loss_player_upper {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)
    {before after : GateGroupPlacement} (source : GateGroupReadout p g kind upper u before)
    (target : GateGroupReadout p g kind upper v after)
    (beforeLegal : before.external.Legal kind) (afterFailed : ¬after.external.Legal kind)
    {d : Direction} (adjacent : Adjacent d u.player v.player) : v.player.2.val < p.D := by
  have endpoints := gate_endpoints l hg hk
  have side := (placement_gate_shape l hg hk).1
  rcases Shuttle.External.input_loss kind before.external after.external beforeLegal afterFailed with hleft | hmid | hright
  · exact lower_endpoint_loss_player_upper l p hl hM haxes motions _ endpoints.1 side
      source.left_axis target.left_axis hleft.1 hleft.2 adjacent
  · exact gate_middle_loss_player_upper l p hl hM haxes motions hg hk hu hsu hp
      source.core.axis_readout target.core.axis_readout hmid.1 hmid.2 adjacent
  · exact lower_endpoint_loss_player_upper l p hl hM haxes motions _ endpoints.2 side
      source.right_axis target.right_axis hright.1 hright.2 adjacent

end Motion
end PushPuzzle.Push.AcceptanceAxisReadout
