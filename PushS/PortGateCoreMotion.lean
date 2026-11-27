/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateGapMotion
public import PushS.PortGateAxisGapMotion
public import PushS.PortGatePrivateEntry
public import PushS.PortGateTrainUnique
public import PushS.PortEndpointReadoutUnique
public import PushS.PortEndpointReadouts
import all PushS.PortGateAxisTrainReadout

/-! Joint horizontal and middle-axis readouts on the same actual gate and their shrinking private regions. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- The actual horizontal trains and middle-axis readout parameters of one complete gate. -/
structure GateCorePlacement where
  rail : ThreeBlocks
  axis : GateAxisPlacement

/-- Both genuine physical readouts of the same gate state. -/
structure GateCoreReadout (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind) (upper : Endpoint)
    (u : State (p.W + 1) (p.H + 1)) (placement : GateCorePlacement) : Prop where
  rail_shape : GateTrainShape p g kind u placement.rail
  axis_readout : GateAxisReadout p g upper u placement.axis

/-- A real step with joint gate readouts, all horizontal forces, and the core-axis forcing barrier. -/
structure GateCoreStep (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind) (upper : Endpoint)
    (u v : State (p.W + 1) (p.H + 1)) (before after : GateCorePlacement) : Prop where
  before_readout : GateCoreReadout p g kind upper u before
  after_readout : GateCoreReadout p g kind upper v after
  rail_motion : GateTrainMotion p g kind u v before.rail after.rail
  axis_mono (outside : u.player ∉ gateAxisNear p g before.axis.parameter) : after.axis.parameter ≤ before.axis.parameter

/-- The distinguished private cap column is a current G hole. -/
abbrev gateFourInG (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind) (state : GateCorePlacement) : Prop :=
  ((gateTrainPlacement p g state.rail).left : ℤ) - kind.kappa + 1 ≤ 4 ∧
    4 ≤ (gateTrainPlacement p g state.rail).short

/-- G and the closed core near interval, together with the private branch when its cap belongs to G. -/
@[expose] def gateLowCorePrivate (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind) (state : GateCorePlacement) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  (gateLeftGap p g kind (gateTrainPlacement p g state.rail) ∪ gateAxisNear p g state.axis.parameter) ∪
    if gateFourInG p g kind state then gatePrivateCells p (g.left + 1) else ∅

/-- The AND left fault's G, with the branch and connected closed axis near interval when its cap belongs to G. -/
@[expose] def gateAndLeftPrivate (p : Scales.Parameters) (g : Placement) (state : GateCorePlacement) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  gateLeftGap p g .andGate (gateTrainPlacement p g state.rail) ∪
    if gateFourInG p g .andGate state then gatePrivateCells p (g.left + 1) ∪ gateAxisNear p g state.axis.parameter else ∅

namespace GateCoreStep

variable {p : Scales.Parameters} {g : Placement} {kind : Shuttle.Kind} {upper : Endpoint}
  {u v : State (p.W + 1) (p.H + 1)} {before after : GateCorePlacement}

/-- The closed core near interval shrinks whenever its current player is external. -/
theorem axis_near_subset (motion : GateCoreStep p g kind upper u v before after)
    (hout : u.player ∉ gateAxisNear p g before.axis.parameter) :
    gateAxisNear p g after.axis.parameter ⊆ gateAxisNear p g before.axis.parameter := by
  have hm := motion.axis_mono hout
  intro q hq
  obtain ⟨_, hx, hlo, hhi⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, by omega, hhi⟩

private theorem four_preserved (motion : GateCoreStep p g kind upper u v before after)
    (hshape : g.right = g.left + 2) (hout : u.player ∉ gateLeftGap p g kind (gateTrainPlacement p g before.rail))
    (hfour : gateFourInG p g kind after) : gateFourInG p g kind before := by
  have hm := motion.rail_motion.left_parameters_mono hshape hout
  change ((gateTrainPlacement p g after.rail).left : ℤ) - kind.kappa + 1 ≤ 4 ∧
    4 ≤ (gateTrainPlacement p g after.rail).short at hfour
  constructor <;> omega

/-- The complete low-core private region shrinks under a real move from outside it. -/
theorem low_private_subset (motion : GateCoreStep p g kind upper u v before after)
    (hshape : g.right = g.left + 2) (hout : u.player ∉ gateLowCorePrivate p g kind before) :
    gateLowCorePrivate p g kind after ⊆ gateLowCorePrivate p g kind before := by
  have hG : u.player ∉ gateLeftGap p g kind (gateTrainPlacement p g before.rail) :=
    fun h => hout (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hA : u.player ∉ gateAxisNear p g before.axis.parameter :=
    fun h => hout (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  intro q hq
  rcases Finset.mem_union.mp hq with hq | hq
  · rcases Finset.mem_union.mp hq with hq | hq
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (motion.rail_motion.left_gap_subset hshape hG hq))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (motion.axis_near_subset hA hq))
  · by_cases hfour : gateFourInG p g kind after
    · have hprev := motion.four_preserved hshape hG hfour
      rw [ite_eq_left hfour] at hq
      exact Finset.mem_union_right _ (by rw [ite_eq_left hprev]; exact hq)
    · rw [ite_eq_right hfour] at hq
      exact False.elim (Finset.notMem_empty _ hq)

/-- The short-train and low core-axis thresholds persist for an external low-core private region. -/
theorem low_thresholds_preserved (motion : GateCoreStep p g kind upper u v before after)
    (hshape : g.right = g.left + 2) (hout : u.player ∉ gateLowCorePrivate p g kind before)
    (hshort : (gateTrainPlacement p g before.rail).short ≤ 5) (haxis : before.axis.parameter ≤ 1) :
    (gateTrainPlacement p g after.rail).short ≤ 5 ∧ after.axis.parameter ≤ 1 := by
  have hG : u.player ∉ gateLeftGap p g kind (gateTrainPlacement p g before.rail) :=
    fun h => hout (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hA : u.player ∉ gateAxisNear p g before.axis.parameter :=
    fun h => hout (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hp := motion.rail_motion.left_parameters_mono hshape hG
  exact ⟨hp.1.trans hshort, (motion.axis_mono hA).trans haxis⟩

/-- The AND left-fault private region shrinks under a real move from outside it. -/
theorem and_left_private_subset (motion : GateCoreStep p g .andGate upper u v before after)
    (hshape : g.right = g.left + 2) (hout : u.player ∉ gateAndLeftPrivate p g before) :
    gateAndLeftPrivate p g after ⊆ gateAndLeftPrivate p g before := by
  have hG : u.player ∉ gateLeftGap p g .andGate (gateTrainPlacement p g before.rail) :=
    fun h => hout (Finset.mem_union_left _ h)
  intro q hq
  rcases Finset.mem_union.mp hq with hq | hq
  · exact Finset.mem_union_left _ (motion.rail_motion.left_gap_subset hshape hG hq)
  · by_cases hfour : gateFourInG p g .andGate after
    · have hprev := motion.four_preserved hshape hG hfour
      have hA : u.player ∉ gateAxisNear p g before.axis.parameter := fun h =>
        hout (Finset.mem_union_right _ (by rw [ite_eq_left hprev]; exact Finset.mem_union_right _ h))
      rw [ite_eq_left hfour] at hq
      apply Finset.mem_union_right
      rw [ite_eq_left hprev]
      rcases Finset.mem_union.mp hq with hq | hq
      · exact Finset.mem_union_left _ hq
      · exact Finset.mem_union_right _ (motion.axis_near_subset hA hq)
    · rw [ite_eq_right hfour] at hq
      exact False.elim (Finset.notMem_empty _ hq)

/-- The AND left-fault's two defining thresholds persist for an external private region. -/
theorem and_left_thresholds_preserved (motion : GateCoreStep p g .andGate upper u v before after)
    (hshape : g.right = g.left + 2) (hout : u.player ∉ gateAndLeftPrivate p g before)
    (hshort : (gateTrainPlacement p g before.rail).short ≤ 5)
    (hleft : 2 ≤ (gateTrainPlacement p g before.rail).left) :
    (gateTrainPlacement p g after.rail).short ≤ 5 ∧ 2 ≤ (gateTrainPlacement p g after.rail).left := by
  have hG : u.player ∉ gateLeftGap p g .andGate (gateTrainPlacement p g before.rail) :=
    fun h => hout (Finset.mem_union_left _ h)
  have hm := motion.rail_motion.left_parameters_mono hshape hG
  exact ⟨hm.1.trans hshort, hleft.trans hm.2⟩

end GateCoreStep

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- Each successful actual prefix has the joint readout of its actual horizontal rail and middle axis. -/
theorem physicalInstance_gate_core_readout {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : ∃ state, GateCoreReadout p g kind upper u state := by
  obtain ⟨rail, hr⟩ := l.physicalInstance_gate_train_shape p hl hM ha initial target hg hk hsu hut ht
  obtain ⟨axis, hv⟩ := l.physicalInstance_gateAxis_train_readout p hl hM ha initial target hg hk hu hsuSide hp hsu hut ht
  exact ⟨⟨rail, axis⟩, hr, hv⟩

/-- Every actual successful step carries consistent horizontal and middle-axis readouts of the same gate. -/
theorem physicalInstance_gate_core_step {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {before : GateCorePlacement} (readout : GateCoreReadout p g kind upper u before) :
    ∃ after, GateCoreStep p g kind upper u v before after := by
  obtain ⟨rb, ra, rail⟩ := l.physicalInstance_gate_train_motion p hl hM ha initial target hg hk hsu hm hvt ht
  have hrail := rail.before_shape.unique readout.rail_shape
  subst rb
  obtain ⟨vb, va, vertical⟩ := l.physicalInstance_gateAxis_train_motion p hl hM ha initial target hg hk hu hsuSide hp hsu hm hvt ht
  have hbefore := vertical.before_shape.readout vertical.before_positive
  have hafter := vertical.after_shape.readout vertical.after_positive
  have hparam := l.endpoint_axis_parameter_unique p hl hM ha hu
    (hbefore.upper_endpoint hsuSide hp) (readout.axis_readout.upper_endpoint hsuSide hp)
  refine ⟨⟨ra, gateAxisPlacement p upper va⟩, readout, ⟨rail.after_shape, hafter⟩, rail, ?_⟩
  intro hout
  have h := vertical.core_parameter_mono (by simpa only [hparam] using hout)
  simpa only [hparam] using h

end Solution
end PushPuzzle.PushS.PortLayout
