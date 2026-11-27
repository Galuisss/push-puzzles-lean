/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointAxisReadout
public import PushS.PortEndpointHorizontalReadout
public import PushS.PortGateAxisTrainReadout
public import PushS.PortAxisGroups
import all PushS.PortAxisGroups
import all PushS.PortGateIndexing
import all PushS.PortWireIndexing
import all PushS.PortSegments

/-! Both actual readouts at every ordinary endpoint of every successful physical prefix. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- The upper ordinary endpoint of a genuine gate axis has the same ordinary half-axis word. -/
theorem GateAxisReadout.upper_endpoint {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {a : GateAxisPlacement}
    (hr : GateAxisReadout p g upper u a) (hs : upper.side = .upper) (hp : upper.port = g.left + 1) :
    EndpointAxisReadout p upper u a.parameter a.upperShift := by
  refine ⟨hr.upper_budget, ?_⟩
  intro q hx hy
  simp only [hs, ite_true] at hy ⊢
  rw [hp] at hx
  exact hr.upper_holes q hx hy

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
  (e : Endpoint) (he : e ∈ l.endpoints)

local notation "I" => l.physicalInstance p hl hM ha initial target

include he

/-- Every actual ordinary endpoint has its genuine bounded reflected half-axis readout. -/
theorem physicalInstance_endpoint_axis_readout {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : ∃ parameter shift, EndpointAxisReadout p e u parameter shift := by
  cases hs : e.side with
  | lower =>
    obtain ⟨upper, hu, hsuSide, hp⟩ := l.endpoints_upper_exists hl (l.endpoints_port_lt hl he)
    obtain ⟨a, hr⟩ := l.physicalInstance_ordinaryAxis_train_readout p hl hM ha initial target hu he hsuSide hs hp.symm hsu hut ht
    exact ⟨a.lowerParameter, a.lowerShift, hr.lower_endpoint hs hp.symm⟩
  | upper =>
    obtain ⟨groups⟩ := l.axisGroups_nonempty hl (l.endpoints_port_lt hl he)
    have outer (hk : e.port = groups.lower.left ∨ e.port = groups.lower.right) :
        ∃ parameter shift, EndpointAxisReadout p e u parameter shift := by
      obtain ⟨lower, hlow, hls, hlp, _⟩ := placement_outer_endpoint l groups.lower_mem hk
      obtain ⟨a, hr⟩ := l.physicalInstance_ordinaryAxis_train_readout p hl hM ha initial target he hlow hs
        (hls.trans groups.lower_side) hlp hsu hut ht
      exact ⟨a.parameter, a.upperShift, hr.upper_endpoint hs⟩
    rcases groups.lower_port with hleft | hright | ⟨hgate, hmid⟩
    · exact outer (Or.inl hleft)
    · exact outer (Or.inr hright)
    · cases hk : groups.lower.gate with
      | none => simp only [hk, Option.isSome_none, Bool.false_eq_true] at hgate
      | some kind =>
        obtain ⟨a, hr⟩ := l.physicalInstance_gateAxis_train_readout p hl hM ha initial target groups.lower_mem hk he hs hmid hsu hut ht
        exact ⟨a.parameter, a.upperShift, hr.upper_endpoint hs hmid⟩

/-- Every actual ordinary endpoint has the genuine near-horizontal readout of its own full train. -/
theorem physicalInstance_endpoint_horizontal_readout {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : ∃ horizontal, EndpointHorizontalReadout p e u horizontal := by
  obtain ⟨g, hg, hend⟩ := List.mem_flatMap.mp he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hend
  cases hk : g.gate with
  | none =>
    obtain ⟨left, right, hr⟩ := l.physicalInstance_wire_train_readout p hl hM ha initial target hg hk hsu hut ht
    simp only [hk, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] at hend
    rcases hend with rfl | rfl
    · exact ⟨left, hr.left_endpoint hl hg hk⟩
    · exact ⟨right, hr.right_endpoint hl hg hk⟩
  | some kind =>
    obtain ⟨b, hr⟩ := l.physicalInstance_gate_train_shape p hl hM ha initial target hg hk hsu hut ht
    simp only [hk, Option.isSome_some, ite_true] at hend
    rcases hend with rfl | rfl
    · exact ⟨(gateTrainPlacement p g b).left, hr.left_endpoint hl hg hk⟩
    · exact ⟨(gateTrainPlacement p g b).right, hr.right_endpoint hl hg hk⟩

end Solution
end PushPuzzle.PushS.PortLayout
