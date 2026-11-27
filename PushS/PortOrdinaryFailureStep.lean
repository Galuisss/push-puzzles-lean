/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortAxisTrainStep
public import PushS.PortGateOuterFailure
public import PushS.PortGateAxisTrainStep
public import PushS.PortWireTrainStep
public import PushS.PortEndpointReadouts
public import PushS.PortEndpointReadoutUnique
import all PushS.PortAxisGroups
import all PushS.PortGateAxisTrainReadout
import all PushS.PortGateIndexing
import all PushS.PortCoreCrossing
import all PushS.PortSegments

/-! Every real successful step preserves an ordinary W fault whose player starts outside its pocket. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- The actual ordinary W fault, with its complete physical endpoint readouts. -/
structure OrdinaryFaultReadout (p : Scales.Parameters) (e : Endpoint) (u : State (p.W + 1) (p.H + 1)) where
  parameter : ℕ
  shift : ℕ
  horizontal : ℕ
  axis_word : EndpointAxisReadout p e u parameter shift
  axis_failed : 2 ≤ parameter
  horizontal_word : EndpointHorizontalReadout p e u horizontal
  horizontal_failed : horizontal ≤ 1

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
  (e : Endpoint) (he : e ∈ l.endpoints)

local notation "I" => l.physicalInstance p hl hM ha initial target

include he

/-- An actual endpoint's failed axis supply persists through its next real step from outside its pocket. -/
theorem physicalInstance_endpoint_axis_failure_step {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) {parameter shift : ℕ}
    (hr : EndpointAxisReadout p e u parameter shift) (hbad : 2 ≤ parameter)
    (hout : u.player ∉ ordinaryPocket p e) :
    ∃ nextParameter nextShift, EndpointAxisReadout p e v nextParameter nextShift ∧ 2 ≤ nextParameter := by
  cases hs : e.side with
  | lower =>
    obtain ⟨upper, hu, hsuSide, hp⟩ := l.endpoints_upper_exists hl (l.endpoints_port_lt hl he)
    obtain ⟨before, after, motion⟩ := l.physicalInstance_ordinaryAxis_train_motion p hl hM ha initial target
      hu he hsuSide hs hp.symm hsu hm hvt ht
    have hsource := motion.before_readout.lower_endpoint hs hp.symm
    have htarget := motion.after_readout.lower_endpoint hs hp.symm
    have heq := l.endpoint_axis_parameter_unique p hl hM ha he hr hsource
    exact ⟨_, _, htarget, motion.lower_fault_preserved hs hp.symm (by rwa [← heq]) hout⟩
  | upper =>
    obtain ⟨groups⟩ := l.axisGroups_nonempty hl (l.endpoints_port_lt hl he)
    have ordinary (hk : e.port = groups.lower.left ∨ e.port = groups.lower.right) :
        ∃ nextParameter nextShift, EndpointAxisReadout p e v nextParameter nextShift ∧ 2 ≤ nextParameter := by
      obtain ⟨lower, hlow, hls, hlp, _⟩ := placement_outer_endpoint l groups.lower_mem hk
      obtain ⟨before, after, motion⟩ := l.physicalInstance_ordinaryAxis_train_motion p hl hM ha initial target
        he hlow hs (hls.trans groups.lower_side) hlp hsu hm hvt ht
      have hsource := motion.before_readout.upper_endpoint hs
      have htarget := motion.after_readout.upper_endpoint hs
      have heq := l.endpoint_axis_parameter_unique p hl hM ha he hr hsource
      exact ⟨_, _, htarget, motion.upper_fault_preserved hs (by rwa [← heq]) hout⟩
    rcases groups.lower_port with hleft | hright | ⟨hgate, hmid⟩
    · exact ordinary (Or.inl hleft)
    · exact ordinary (Or.inr hright)
    · cases hk : groups.lower.gate with
      | none => simp only [hk, Option.isSome_none, Bool.false_eq_true] at hgate
      | some kind =>
        obtain ⟨before, after, motion⟩ := l.physicalInstance_gateAxis_train_motion p hl hM ha initial target
          groups.lower_mem hk he hs hmid hsu hm hvt ht
        have hsource := (motion.before_shape.readout motion.before_positive).upper_endpoint hs hmid
        have htarget := (motion.after_shape.readout motion.after_positive).upper_endpoint hs hmid
        have heq := l.endpoint_axis_parameter_unique p hl hM ha he hr hsource
        exact ⟨_, _, htarget, motion.upper_fault_preserved hs hmid (by rwa [← heq]) hout⟩

/-- An actual endpoint's failed horizontal supply persists through its next real step from outside its pocket. -/
theorem physicalInstance_endpoint_horizontal_failure_step {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) {horizontal : ℕ}
    (hr : EndpointHorizontalReadout p e u horizontal) (hbad : horizontal ≤ 1)
    (hout : u.player ∉ ordinaryPocket p e) :
    ∃ nextHorizontal, EndpointHorizontalReadout p e v nextHorizontal ∧ nextHorizontal ≤ 1 := by
  obtain ⟨g, hg, hend⟩ := List.mem_flatMap.mp he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hend
  cases hk : g.gate with
  | none =>
    obtain ⟨motion⟩ := l.physicalInstance_wire_train_step p hl hM ha initial target hg hk hsu hm hvt ht
    have hsource := motion.source_shape.readout motion.marked.length_pos
    have htarget := motion.target_shape.readout motion.marked.length_pos
    simp only [hk, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] at hend
    rcases hend with rfl | rfl
    · have hs := hsource.left_endpoint hl hg hk
      have hv := htarget.left_endpoint hl hg hk
      have hb := (l.endpoint_horizontal_failed_iff p hl ha he hr hs).mp hbad
      exact ⟨_, hv, motion.left_fault_preserved hb hout⟩
    · have hs := hsource.right_endpoint hl hg hk
      have hv := htarget.right_endpoint hl hg hk
      have hb := (l.endpoint_horizontal_failed_iff p hl ha he hr hs).mp hbad
      exact ⟨_, hv, motion.right_fault_preserved hb hout⟩
  | some kind =>
    obtain ⟨before, after, motion⟩ := l.physicalInstance_gate_train_motion p hl hM ha initial target hg hk hsu hm hvt ht
    have hside := (placement_gate_shape l hg hk).1
    have hlevel := gate_level_one l hg hk
    simp only [hk, Option.isSome_some, ite_true] at hend
    rcases hend with rfl | rfl
    · have hs := motion.before_shape.left_endpoint hl hg hk
      have hv := motion.after_shape.left_endpoint hl hg hk
      have hb := (l.endpoint_horizontal_failed_iff p hl ha he hr hs).mp hbad
      exact ⟨_, hv, motion.left_wire_fault_preserved hside hlevel hb hout⟩
    · have hs := motion.before_shape.right_endpoint hl hg hk
      have hv := motion.after_shape.right_endpoint hl hg hk
      have hb := (l.endpoint_horizontal_failed_iff p hl ha he hr hs).mp hbad
      exact ⟨_, hv, motion.right_wire_fault_preserved hside hlevel hb hout⟩

/-- One native successful step preserves the actual complete W fault and keeps its player outside. -/
theorem physicalInstance_ordinary_failure_step {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    (fault : OrdinaryFaultReadout p e u) (hout : u.player ∉ ordinaryPocket p e) :
    ∃ _ : OrdinaryFaultReadout p e v, v.player ∉ ordinaryPocket p e := by
  have hplayer := l.physicalInstance_ordinary_failure_no_entry p hl hM ha initial target e he hsu hm hvt ht
    fault.axis_word fault.axis_failed fault.horizontal_word fault.horizontal_failed hout
  obtain ⟨parameter, shift, haxis, hbadAxis⟩ := l.physicalInstance_endpoint_axis_failure_step p hl hM ha initial target e he
    hsu hm hvt ht fault.axis_word fault.axis_failed hout
  obtain ⟨horizontal, hread, hbadHorizontal⟩ := l.physicalInstance_endpoint_horizontal_failure_step p hl hM ha initial target e he
    hsu hm hvt ht fault.horizontal_word fault.horizontal_failed hout
  exact ⟨⟨parameter, shift, horizontal, haxis, hbadAxis, hread, hbadHorizontal⟩, hplayer⟩

end Solution
end PushPuzzle.PushS.PortLayout
