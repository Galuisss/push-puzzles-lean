/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateCorePrivate
public import Push.AcceptanceOrdinaryFailureTrace
public import PushS.PortGateCoreFailure
import all PushS.PortGateCoreFailure
import all PushS.PortGateIndexing

/-! Genuine accepted core motions preserve low-core and AND-left faults along the same actual suffix. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram AcceptanceAxisReadout

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM ha initial target

include hgate

/-- An actual successful step preserves the complete OR/AND-center fault and its external player. -/
private theorem canonical_gate_low_core_failure_step_of_motions {g : Placement}
    (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axis : AxisMotions l p u v) (rails : RailMotions l p (I).board u v)
    {state : GateCorePlacement} (fault : GateLowCoreFault p g kind upper u state) :
    ∃ after, GateLowCoreFault p g kind upper v after := by
  obtain ⟨after, motion⟩ := gate_core_step_of_motions l p hl hM ha axis rails hg hk hu hsuSide hp fault.readout
  have hshape := (placement_gate_shape l hg hk).2
  have hbound : -1 ≤ ((gateTrainPlacement p g state.rail).left : ℤ) - kind.kappa + 1 := by
    cases kind with
    | andGate => change -1 ≤ ((gateTrainPlacement p g state.rail).left : ℤ) - 2 + 1; omega
    | orGate =>
      have h := fault.left_if_or rfl
      change -1 ≤ ((gateTrainPlacement p g state.rail).left : ℤ) - 4 + 1
      omega
  have hout := canonical_gate_low_private_no_entry l p hl hM ha initial target hgate hg hk hsu hm hvt accepted
    fault.readout hbound fault.short (Or.inl fault.axis_low) fault.outside
  have hthreshold := motion.low_thresholds_preserved hshape fault.outside fault.short fault.axis_low
  have hG : u.player ∉ gateLeftGap p g kind (gateTrainPlacement p g state.rail) :=
    fun h => fault.outside (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hleft := motion.rail_motion.left_parameters_mono hshape hG
  exact ⟨after, motion.after_readout, hthreshold.1, hthreshold.2,
    fun h => (fault.left_if_or h).trans hleft.2, fun h => hout (motion.low_private_subset hshape fault.outside h)⟩

/-- An actual successful step preserves the complete AND-left fault and its external player. -/
private theorem canonical_gate_and_left_failure_step_of_motions {g : Placement}
    (hg : g ∈ placements l)
    (hk : g.gate = some .andGate) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axis : AxisMotions l p u v) (rails : RailMotions l p (I).board u v)
    {state : GateCorePlacement} (fault : GateAndLeftFault p g upper u state) :
    ∃ after, GateAndLeftFault p g upper v after := by
  obtain ⟨after, motion⟩ := gate_core_step_of_motions l p hl hM ha axis rails hg hk hu hsuSide hp fault.readout
  have hshape := (placement_gate_shape l hg hk).2
  have hout := canonical_gate_and_left_private_no_entry l p hl hM ha initial target hgate hg hk hsu hm hvt accepted
    fault.readout fault.left fault.short fault.outside
  have hthreshold := motion.and_left_thresholds_preserved hshape fault.outside fault.short fault.left
  exact ⟨after, motion.after_readout, hthreshold.1, hthreshold.2,
    fun h => hout (motion.and_left_private_subset hshape fault.outside h)⟩

/-- The complete actual suffix preserves OR/AND-center faults and their inaccessible current private region. -/
theorem canonical_gate_low_core_failure_suffix_of_dynamics {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (dynamics : AcceptanceOrdinaryFailure.Dynamics l p (I).board (I).initial t) {state : GateCorePlacement} (fault : GateLowCoreFault p g kind upper u state) :
    ∃ after, GateLowCoreFault p g kind upper t after := by
  apply readout_suffix hut (GateLowCoreFault p g kind upper) ?_ fault
  intro x y hux hxy hyt before hf
  exact canonical_gate_low_core_failure_step_of_motions l p hl hM ha initial target hgate hg hk hu hsuSide hp
    (hsu.trans hux) hxy hyt accepted (dynamics.axis (hsu.trans hux) hxy hyt)
    (dynamics.rail (hsu.trans hux) hxy hyt) hf

/-- The complete actual suffix preserves AND-left faults and their inaccessible current private region. -/
theorem canonical_gate_and_left_failure_suffix_of_dynamics {g : Placement} (hg : g ∈ placements l)
    (hk : g.gate = some .andGate) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (dynamics : AcceptanceOrdinaryFailure.Dynamics l p (I).board (I).initial t) {state : GateCorePlacement} (fault : GateAndLeftFault p g upper u state) :
    ∃ after, GateAndLeftFault p g upper t after := by
  apply readout_suffix hut (GateAndLeftFault p g upper) ?_ fault
  intro x y hux hxy hyt before hf
  exact canonical_gate_and_left_failure_step_of_motions l p hl hM ha initial target hgate hg hk hu hsuSide hp
    (hsu.trans hux) hxy hyt accepted (dynamics.axis (hsu.trans hux) hxy hyt)
    (dynamics.rail (hsu.trans hux) hxy hyt) hf

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
