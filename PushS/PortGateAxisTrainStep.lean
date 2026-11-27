/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateAxisTrainReadout
public import PushS.PortOrdinaryFailure
public import PushS.TwoTrainStep
import all PushS.PortGateAxisTrainReadout

/-! Actual gate-axis train motion and persistence of the failed upper ordinary axis supply. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- One actual gate-axis step with both rigid layouts and their genuine forcing coordinates. -/
structure GateAxisTrainMotion (p : Scales.Parameters) (g : Placement) (upper : Endpoint)
    (u v : State (p.W + 1) (p.H + 1)) (before after : TwoBlocks) : Prop where
  before_shape : GateAxisTrainShape p g upper u before
  after_shape : GateAxisTrainShape p g upper v after
  before_positive : before.Positive
  after_positive : after.Positive
  player_column (changed : before.first ≠ after.first ∨ before.last ≠ after.last) : u.player.1.val = p.x (g.left + 1)
  first_bounds : before.first - 1 ≤ after.first ∧ after.first ≤ before.first + 1
  last_bounds : before.last - 1 ≤ after.last ∧ after.last ≤ before.last + 1
  first_forward (moved : before.first < after.first) : (u.player.2.val : ℤ) = before.first - 1
  first_backward (moved : after.first < before.first) : (u.player.2.val : ℤ) = before.first + before.firstLength
  last_forward (moved : before.last < after.last) : (u.player.2.val : ℤ) = before.last - 1
  last_backward (moved : after.last < before.last) : (u.player.2.val : ℤ) = before.last + before.lastLength

/-- An upper ordinary axis fault cannot recover while the actual player remains outside its three-cell pocket. -/
theorem GateAxisTrainMotion.upper_fault_preserved {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
    {u v : State (p.W + 1) (p.H + 1)} {before after : TwoBlocks}
    (motion : GateAxisTrainMotion p g upper u v before after) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)
    (hbad : 2 ≤ (gateAxisPlacement p upper before).parameter) (hout : u.player ∉ ordinaryPocket p upper) :
    2 ≤ (gateAxisPlacement p upper after).parameter := by
  have hb := motion.before_shape.placement_coordinates motion.before_positive
  have ha := motion.after_shape.placement_coordinates motion.after_positive
  by_contra hfail
  have hmove : before.last < after.last := by omega
  have hy := motion.last_forward hmove
  have hx := motion.player_column (Or.inr (ne_of_lt hmove))
  have hxp : u.player.1.val = p.x upper.port := by simpa only [hp] using hx
  apply hout
  rw [ordinaryPocket, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, Or.inl ⟨?_, ?_⟩⟩
  · split <;> omega
  · simp only [hsu, ite_true]
    omega

private theorem shape_of_line (p : Scales.Parameters) (g : Placement) (upper : Endpoint)
    (initial : SignalState) (hpos : (gateAxisTrainBlocks p upper initial).Positive)
    (T : LineState (Fin (gateAxisTrainBlocks p upper initial).size) (p.W + 1) (p.H + 1) .south (p.x (g.left + 1)))
    (s : State (p.W + 1) (p.H + 1)) (hstate : T.state = BoxMask.keep s (gateAxis p (g.left + 1)))
    (hgap : ((gateAxisTrainBlocks p upper initial).atState hpos T).Gapped)
    (hs : (lineBoxes .south (p.x (g.left + 1)) T.state).image Direction.south.position =
      ((gateAxisTrainBlocks p upper initial).atState hpos T).slots) :
    GateAxisTrainShape p g upper s ((gateAxisTrainBlocks p upper initial).atState hpos T) := by
  refine ⟨rfl, rfl, hgap, ?_⟩
  rw [hstate, BoxMask.lineBoxes_keep] at hs
  · exact hs
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- A successful gate-axis step lifts with the original two train marks on both sides. -/
theorem physicalInstance_gateAxis_train_marked_step {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    Nonempty (TwoBlocks.MarkedStep (gateAxisTrainBlocks p upper initial) (l.gateAxisTrainBlocks_positive p hl hM hu initial)
      (I).board none .south (p.x (g.left + 1)) (BoxMask.keep u (gateAxis p (g.left + 1))) (BoxMask.keep v (gateAxis p (g.left + 1)))) := by
  let b := gateAxisTrainBlocks p upper initial
  let c := gateAxisTrainBlocks p upper target
  have hpre := l.physicalInstance_gateAxis_admissible_prefix p hl hM ha initial target hg hk hsu
    ((Relation.ReflTransGen.single hm).trans hvt) ht
  have hpost := l.physicalInstance_gateAxis_admissible_suffix p hl hM ha initial target hg hk (hsu.tail hm) hvt ht
  have hstep := BoxMask.keep_admissible (axis := .south) (lane := p.x (g.left + 1)) (gateAxis_runClosed p (g.left + 1))
    (fun _ hq => (Finset.mem_filter.mp hq).2.1) hm
    (l.physicalInstance_gateAxis_inventory_step p hl hM ha initial target hg hk hsu hm hvt ht)
  exact b.admissible_step (l.gateAxisTrainBlocks_positive p hl hM hu initial) (l.gateAxisTrainBlocks_gapped p hl hM hu initial)
    c.first c.last (l.gateAxisTrainBlocks_gapped p hl hM hu target) hpre hstep hpost
    (l.physicalInstance_gateAxis_train_initial_slots p hl hM ha initial target hg hk hu hsuSide hp)
    (l.physicalInstance_gateAxis_train_target_slots p hl hM ha initial target hg hk hu hsuSide hp ht)

/-- Every successful gate-axis step has both genuine rigid layouts and all actual player forcing coordinates. -/
theorem physicalInstance_gateAxis_train_motion {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    ∃ before after, GateAxisTrainMotion p g upper u v before after := by
  obtain ⟨m⟩ := l.physicalInstance_gateAxis_train_marked_step p hl hM ha initial target hg hk hu hsuSide hp hsu hm hvt ht
  have hpos := l.gateAxisTrainBlocks_positive p hl hM hu initial
  refine ⟨m.beforeBlocks, m.afterBlocks,
    shape_of_line p g upper initial _ m.before u m.before_state m.before_gapped m.before_slots,
    shape_of_line p g upper initial _ m.after v m.after_state m.after_gapped m.after_slots,
    hpos, hpos, m.player_lane, ?_, ?_, m.first_forward, m.first_backward, m.last_forward, m.last_backward⟩
  · exact m.step.coordinate_bounds ⟨0, by dsimp only [TwoBlocks.size]; have h := hpos.1; omega⟩
  · exact m.step.coordinate_bounds ⟨(gateAxisTrainBlocks p upper initial).firstLength, by
      dsimp only [TwoBlocks.size]; have h := hpos.2; omega⟩

end Solution
end PushPuzzle.PushS.PortLayout
