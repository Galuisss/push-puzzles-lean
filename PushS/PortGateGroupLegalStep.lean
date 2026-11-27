/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateGroupReadout
public import PushS.PortGateRegionBounds
public import PushS.PortGateCoreFailure
public import PushS.PortGateRelayFailure
public import PushS.PortOrdinaryFailureAbsent
import all PushS.PortGateIndexing

/-! A lower gate's first external input failure is excluded by its actual physical fault trap. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial : SignalState)
  (axes : List Bool) (hlegal : l.InputLegal axes)

local notation "I" => l.physicalInstance p hl hM ha initial (l.canonical axes)

include hlegal

/-- Every actual successful step preserves each lower AND/OR group's complete external input threshold. -/
theorem physicalInstance_gate_group_legal_step {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {before after : GateGroupPlacement} (hb : GateGroupReadout p g kind upper u before)
    (hc : GateGroupReadout p g kind upper v after) (hbefore : before.external.Legal kind) : after.external.Legal kind := by
  by_contra hbad
  have hy := l.physicalInstance_gate_group_loss_player_upper p hl hM ha initial (l.canonical axes) hg hk hu hsuSide hp
    hsu hm hvt ht hb hc hbefore hbad
  have he := gate_endpoints l hg hk
  have houtR : v.player ∉ gateRightGap p g (gateTrainPlacement p g after.core.rail) := by
    intro h
    have hh := gateRightGap_below_midline p g _ h
    omega
  have houtC : v.player ∉ gateLowCorePrivate p g kind after.core := by
    intro h
    have hh := gateLowCorePrivate_below_midline p g kind after.core hc.core.axis_readout.parameter_le h
    omega
  have fault := Shuttle.fault_of_illegal kind (gateTrainPlacement p g after.core.rail) after.external hbad
  cases fault with
  | leftWire haxis hhorizontal =>
    have hf : OrdinaryFaultReadout p ⟨g.side, g.left, true, g.level, g.internal⟩ v :=
      ⟨after.leftParameter, after.leftShift, (gateTrainPlacement p g after.core.rail).left,
        hc.left_axis, haxis, hc.core.rail_shape.left_endpoint hl hg hk, hhorizontal⟩
    exact l.physicalInstance_ordinary_failure_absent p hl hM ha initial axes hlegal _ he.1 (hsu.tail hm) hvt ht ⟨hf⟩
  | rightWire haxis hhorizontal =>
    have hf : OrdinaryFaultReadout p ⟨g.side, g.right, false, g.level, g.internal + 2⟩ v :=
      ⟨after.rightParameter, after.rightShift, (gateTrainPlacement p g after.core.rail).right,
        hc.right_axis, haxis, hc.core.rail_shape.right_endpoint hl hg hk, hhorizontal⟩
    exact l.physicalInstance_ordinary_failure_absent p hl hM ha initial axes hlegal _ he.2 (hsu.tail hm) hvt ht ⟨hf⟩
  | relay hshort hright =>
    exact l.physicalInstance_gate_relay_failure_impossible p hl hM ha initial axes hg hk (hsu.tail hm) hvt ht
      ⟨hc.core.rail_shape, hshort, hright, houtR⟩
  | orCore _ hleft hshort haxis =>
    exact l.physicalInstance_gate_low_core_failure_impossible p hl hM ha initial axes hlegal hg hk hu hsuSide hp
      (hsu.tail hm) hvt ht ⟨hc.core, hshort, haxis, fun _ => hleft, houtC⟩
  | andCenter hkind hshort haxis =>
    subst kind
    exact l.physicalInstance_gate_low_core_failure_impossible p hl hM ha initial axes hlegal hg hk hu hsuSide hp
      (hsu.tail hm) hvt ht ⟨hc.core, hshort, haxis, (fun h => nomatch h), houtC⟩
  | andLeft hkind hshort hleft =>
    subst kind
    have houtL : v.player ∉ gateAndLeftPrivate p g after.core := by
      intro h
      have hh := gateAndLeftPrivate_below_midline p g after.core hc.core.axis_readout.parameter_le h
      omega
    exact l.physicalInstance_gate_and_left_failure_impossible p hl hM ha initial axes hlegal hg hk hu hsuSide hp
      (hsu.tail hm) hvt ht ⟨hc.core, hshort, hleft, houtL⟩

end Solution
end PushPuzzle.PushS.PortLayout
