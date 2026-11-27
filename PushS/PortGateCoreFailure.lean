/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateCorePrivate
public import PushS.PortGateCoreTarget
import all PushS.PortGateIndexing
import all PushS.PortBackground

/-! Complete actual O, AND-center and AND-left traps along the original successful physical suffix. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- OR or AND-center failure with an external player and both actual joint physical readouts. -/
structure GateLowCoreFault (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind) (upper : Endpoint)
    (u : State (p.W + 1) (p.H + 1)) (state : GateCorePlacement) : Prop where
  readout : GateCoreReadout p g kind upper u state
  short : (gateTrainPlacement p g state.rail).short ≤ 5
  axis_low : state.axis.parameter ≤ 1
  left_if_or : kind = .orGate → 2 ≤ (gateTrainPlacement p g state.rail).left
  outside : u.player ∉ gateLowCorePrivate p g kind state

/-- AND-left failure with an external player and both actual joint physical readouts. -/
structure GateAndLeftFault (p : Scales.Parameters) (g : Placement) (upper : Endpoint)
    (u : State (p.W + 1) (p.H + 1)) (state : GateCorePlacement) : Prop where
  readout : GateCoreReadout p g .andGate upper u state
  short : (gateTrainPlacement p g state.rail).short ≤ 5
  left : 2 ≤ (gateTrainPlacement p g state.rail).left
  outside : u.player ∉ gateAndLeftPrivate p g state

private theorem readout_suffix {α β : Type} {r : α → α → Prop} {s t : α}
    (hr : Relation.ReflTransGen r s t) (P : α → β → Prop)
    (hstep : ∀ u v, Relation.ReflTransGen r s u → r u v → Relation.ReflTransGen r v t →
      ∀ before, P u before → ∃ after, P v after) {before : β} (hf : P s before) : ∃ after, P t after := by
  have hp : Relation.ReflTransGen (fun u v => ∀ before, P u before → ∃ after, P v after) s t :=
    enrich_path hr hstep
  clear hr hstep
  induction hp with
  | refl => exact ⟨before, hf⟩
  | tail _ hm ih => obtain ⟨c, hc⟩ := ih; exact hm c hc

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- An actual successful step preserves the complete OR/AND-center fault and its external player. -/
theorem physicalInstance_gate_low_core_failure_step {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {state : GateCorePlacement} (fault : GateLowCoreFault p g kind upper u state) :
    ∃ after, GateLowCoreFault p g kind upper v after := by
  obtain ⟨after, motion⟩ := l.physicalInstance_gate_core_step p hl hM ha initial target hg hk hu hsuSide hp hsu hm hvt ht fault.readout
  have hshape := (placement_gate_shape l hg hk).2
  have hbound : -1 ≤ ((gateTrainPlacement p g state.rail).left : ℤ) - kind.kappa + 1 := by
    cases kind with
    | andGate => change -1 ≤ ((gateTrainPlacement p g state.rail).left : ℤ) - 2 + 1; omega
    | orGate =>
      have h := fault.left_if_or rfl
      change -1 ≤ ((gateTrainPlacement p g state.rail).left : ℤ) - 4 + 1
      omega
  have hout := l.physicalInstance_gate_low_private_no_entry p hl hM ha initial target hg hk hsu hm hvt ht
    fault.readout hbound fault.short (Or.inl fault.axis_low) fault.outside
  have hthreshold := motion.low_thresholds_preserved hshape fault.outside fault.short fault.axis_low
  have hG : u.player ∉ gateLeftGap p g kind (gateTrainPlacement p g state.rail) :=
    fun h => fault.outside (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hleft := motion.rail_motion.left_parameters_mono hshape hG
  exact ⟨after, motion.after_readout, hthreshold.1, hthreshold.2,
    fun h => (fault.left_if_or h).trans hleft.2, fun h => hout (motion.low_private_subset hshape fault.outside h)⟩

/-- An actual successful step preserves the complete AND-left fault and its external player. -/
theorem physicalInstance_gate_and_left_failure_step {g : Placement} (hg : g ∈ placements l)
    (hk : g.gate = some .andGate) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {state : GateCorePlacement} (fault : GateAndLeftFault p g upper u state) :
    ∃ after, GateAndLeftFault p g upper v after := by
  obtain ⟨after, motion⟩ := l.physicalInstance_gate_core_step p hl hM ha initial target hg hk hu hsuSide hp hsu hm hvt ht fault.readout
  have hshape := (placement_gate_shape l hg hk).2
  have hout := l.physicalInstance_gate_and_left_private_no_entry p hl hM ha initial target hg hk hsu hm hvt ht
    fault.readout fault.left fault.short fault.outside
  have hthreshold := motion.and_left_thresholds_preserved hshape fault.outside fault.short fault.left
  exact ⟨after, motion.after_readout, hthreshold.1, hthreshold.2,
    fun h => hout (motion.and_left_private_subset hshape fault.outside h)⟩

/-- The complete actual suffix preserves OR/AND-center faults and their inaccessible current private region. -/
theorem physicalInstance_gate_low_core_failure_suffix {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) {state : GateCorePlacement} (fault : GateLowCoreFault p g kind upper u state) :
    ∃ after, GateLowCoreFault p g kind upper t after := by
  apply readout_suffix hut (GateLowCoreFault p g kind upper) ?_ fault
  intro x y hux hxy hyt before hf
  exact l.physicalInstance_gate_low_core_failure_step p hl hM ha initial target hg hk hu hsuSide hp
    (hsu.trans hux) hxy hyt ht hf

/-- The complete actual suffix preserves AND-left faults and their inaccessible current private region. -/
theorem physicalInstance_gate_and_left_failure_suffix {g : Placement} (hg : g ∈ placements l)
    (hk : g.gate = some .andGate) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) {state : GateCorePlacement} (fault : GateAndLeftFault p g upper u state) :
    ∃ after, GateAndLeftFault p g upper t after := by
  apply readout_suffix hut (GateAndLeftFault p g upper) ?_ fault
  intro x y hux hxy hyt before hf
  exact l.physicalInstance_gate_and_left_failure_step p hl hM ha initial target hg hk hu hsuSide hp
    (hsu.trans hux) hxy hyt ht hf

end Solution

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial : SignalState)
  (axes : List Bool) (hlegal : l.InputLegal axes)

local notation "I" => l.physicalInstance p hl hM ha initial (l.canonical axes)

include hlegal

/-- No external OR/AND-center fault can reach a legal complete canonical goal on the actual board. -/
theorem physicalInstance_gate_low_core_failure_impossible {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) {state : GateCorePlacement} (fault : GateLowCoreFault p g kind upper u state) : False := by
  obtain ⟨after, hf⟩ := l.physicalInstance_gate_low_core_failure_suffix p hl hM ha initial (l.canonical axes)
    hg hk hu hsuSide hp hsu hut ht fault
  have hc := l.physicalInstance_gate_core_target_readout p hl hM ha initial axes hg hk hu hsuSide hp ht
  have hr := hf.readout.rail_shape.unique hc.rail_shape
  have hv := hf.readout.parameter_unique hc hl hM ha hu hsuSide hp
  have hs := hf.short
  have ha' := hf.axis_low
  have hl' := hf.left_if_or
  rw [hr] at hs hl'
  rw [hv] at ha'
  exact l.canonical_gate_no_low_core_fault p axes hlegal hg hk upper hp ⟨hs, ha', hl'⟩

/-- No external AND-left fault can reach a legal complete canonical goal on the actual board. -/
theorem physicalInstance_gate_and_left_failure_impossible {g : Placement} (hg : g ∈ placements l)
    (hk : g.gate = some .andGate) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) {state : GateCorePlacement} (fault : GateAndLeftFault p g upper u state) : False := by
  obtain ⟨after, hf⟩ := l.physicalInstance_gate_and_left_failure_suffix p hl hM ha initial (l.canonical axes)
    hg hk hu hsuSide hp hsu hut ht fault
  have hc := l.physicalInstance_gate_core_target_readout p hl hM ha initial axes hg hk hu hsuSide hp ht
  have hr := hf.readout.rail_shape.unique hc.rail_shape
  have hs := hf.short
  have hl' := hf.left
  rw [hr] at hs hl'
  exact l.canonical_gate_no_and_left_fault p axes hlegal hg hk upper hp ⟨hs, hl'⟩

end Canonical
end PushPuzzle.PushS.PortLayout
