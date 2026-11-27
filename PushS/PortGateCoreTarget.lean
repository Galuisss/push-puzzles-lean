/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateCoreMotion
public import PushS.PortCanonicalSignals
import all PushS.PortGateAxisTrainReadout

/-! Joint physical target readouts and exclusion of all low-core and AND-left faults in canonical legal targets. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- The literal joint target placement of a canonical complete gate. -/
@[expose] def canonicalGateCorePlacement (l : PortLayout) (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind)
    (upper : Endpoint) (axes : List Bool) : GateCorePlacement where
  rail := gateTrainBlocks p g kind (l.canonical axes)
  axis := gateAxisPlacement p upper (gateAxisTrainBlocks p upper (l.canonical axes))

/-- Two genuine joint readouts of the same actual gate have the same middle-axis parameter. -/
theorem GateCoreReadout.parameter_unique {l : PortLayout} {p : Scales.Parameters} {g : Placement} {kind : Shuttle.Kind}
    {upper : Endpoint} {u : State (p.W + 1) (p.H + 1)} {a c : GateCorePlacement}
    (hb : GateCoreReadout p g kind upper u a) (hc : GateCoreReadout p g kind upper u c)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1) :
    a.axis.parameter = c.axis.parameter :=
  l.endpoint_axis_parameter_unique p hl hM ha hu (hb.axis_readout.upper_endpoint hsu hp) (hc.axis_readout.upper_endpoint hsu hp)

/-- A solved actual gate has the joint literal canonical target readout. -/
theorem physicalInstance_gate_core_target_readout (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial : SignalState) (axes : List Bool) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsu : upper.side = .upper) (hp : upper.port = g.left + 1) {t : State (p.W + 1) (p.H + 1)}
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial (l.canonical axes)).board.goals) :
    GateCoreReadout p g kind upper t (canonicalGateCorePlacement l p g kind upper axes) := by
  have hv : GateAxisTrainShape p g upper t (gateAxisTrainBlocks p upper (l.canonical axes)) := by
    refine ⟨rfl, rfl, l.gateAxisTrainBlocks_gapped p hl hM hu (l.canonical axes), ?_⟩
    have hs := l.physicalInstance_gateAxis_train_target_slots p hl hM ha initial (l.canonical axes) hg hk hu hsu hp ht
    change (lineBoxes .south (p.x (g.left + 1)) (BoxMask.keep t (gateAxis p (g.left + 1)))).image Direction.south.position = _ at hs
    rw [BoxMask.lineBoxes_keep] at hs
    · exact hs
    · intro q hq
      exact (Finset.mem_filter.mp hq).2.1
  exact ⟨l.physicalInstance_gate_train_target_shape p hl hM ha initial (l.canonical axes) hg hk ht,
    hv.readout (l.gateAxisTrainBlocks_positive p hl hM hu (l.canonical axes))⟩

/-- Canonical left, short and core-axis parameters read the original three actual interface bits. -/
theorem canonical_gate_core_values (l : PortLayout) (p : Scales.Parameters) (axes : List Bool)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (upper : Endpoint) (hp : upper.port = g.left + 1) :
    let state := canonicalGateCorePlacement l p g kind upper axes
    (gateTrainPlacement p g state.rail).left = 1 + (axes.getD g.left false).toNat ∧
      (gateTrainPlacement p g state.rail).short = (if axes.getD g.right false then 1 else 6 : ℤ) ∧
      state.axis.parameter = if axes.getD (g.left + 1) false then 1 else 2 := by
  have hread := l.canonical_gate_read axes hg hk
  constructor
  · dsimp only [canonicalGateCorePlacement, gateTrainPlacement, gateTrainBlocks]
    rw [hread.1]
    cases axes.getD g.left false <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  · constructor
    · dsimp only [canonicalGateCorePlacement, gateTrainPlacement, gateTrainBlocks]
      rw [hread.2.1]
      cases axes.getD g.right false <;>
        simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false] <;> omega
    · change (((readDepth p upper.level : ℤ) + 4 - ((readDepth p upper.level : ℤ) + 2 +
        (axes.getD upper.port false).toNat)).toNat) = _
      rw [hp]
      cases axes.getD (g.left + 1) false <;>
        simp only [Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true, ite_true, ite_false] <;> omega

private theorem short_bit {b : Bool} (h : (if b then 1 else 6 : ℤ) ≤ 5) : b = true := by
  cases b <;> simp_all

private theorem axis_bit {b : Bool} (h : (if b then 1 else 2 : ℕ) ≤ 1) : b = true := by
  cases b <;> simp_all

private theorem left_bit {b : Bool} (h : 2 ≤ 1 + b.toNat) : b = true := by
  cases b <;> simp_all

/-- A legal canonical gate excludes both OR and AND center faults with a low middle-axis parameter. -/
theorem canonical_gate_no_low_core_fault (l : PortLayout) (p : Scales.Parameters) (axes : List Bool)
    (hlegal : l.InputLegal axes) {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (upper : Endpoint) (hp : upper.port = g.left + 1) :
    let state := canonicalGateCorePlacement l p g kind upper axes
    ¬ ((gateTrainPlacement p g state.rail).short ≤ 5 ∧ state.axis.parameter ≤ 1 ∧
      (kind = .orGate → 2 ≤ (gateTrainPlacement p g state.rail).left)) := by
  dsimp only
  intro hbad
  obtain ⟨hl, hs, hv⟩ := l.canonical_gate_core_values p axes hg hk upper hp
  obtain ⟨hshort, haxis, hleft⟩ := hbad
  rw [hs] at hshort
  rw [hv] at haxis
  have hR := short_bit hshort
  have hC := axis_bit haxis
  have hin := hlegal.gate_inputs hg hk
  cases kind with
  | andGate =>
    simp only [ite_true] at hin
    rcases hin with hin | ⟨_, hin⟩
    · rw [hR] at hin; cases hin
    · rw [hC] at hin; cases hin
  | orGate =>
    have hL : axes.getD g.left false = true := by
      have hb := hleft rfl
      rw [hl] at hb
      exact left_bit hb
    simp only [reduceCtorEq, ite_false] at hin
    rcases hin with hin | hin | hin
    · rw [hL] at hin; cases hin
    · rw [hC] at hin; cases hin
    · rw [hR] at hin; cases hin

/-- A legal canonical AND gate excludes the low-short, lost-left-input fault. -/
theorem canonical_gate_no_and_left_fault (l : PortLayout) (p : Scales.Parameters) (axes : List Bool)
    (hlegal : l.InputLegal axes) {g : Placement} (hg : g ∈ placements l) (hk : g.gate = some .andGate)
    (upper : Endpoint) (hp : upper.port = g.left + 1) :
    let state := canonicalGateCorePlacement l p g .andGate upper axes
    ¬ ((gateTrainPlacement p g state.rail).short ≤ 5 ∧ 2 ≤ (gateTrainPlacement p g state.rail).left) := by
  dsimp only
  intro hbad
  obtain ⟨hl, hs, _⟩ := l.canonical_gate_core_values p axes hg hk upper hp
  obtain ⟨hshort, hleft⟩ := hbad
  rw [hs] at hshort
  rw [hl] at hleft
  have hR := short_bit hshort
  have hL := left_bit hleft
  have hin := hlegal.gate_inputs hg hk
  simp only [ite_true] at hin
  rcases hin with hin | ⟨hin, _⟩
  · rw [hR] at hin; cases hin
  · rw [hL] at hin; cases hin

end PushPuzzle.PushS.PortLayout
