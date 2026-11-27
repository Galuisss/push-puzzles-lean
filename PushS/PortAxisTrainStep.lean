/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortAxisTrainReadout
public import PushS.PortOrdinaryFailure
public import PushS.TrainStep
import all PushS.PortAxisTrainReadout

/-! The actual middle train controls both ordinary shared-axis input thresholds. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- One actual ordinary-axis middle-train step, with both complete three-train layouts. -/
structure OrdinaryAxisMotion (p : Scales.Parameters) (upper lower : Endpoint)
    (u v : State (p.W + 1) (p.H + 1)) (before after : ThreeBlocks) : Prop where
  before_shape : OrdinaryAxisTrainShape p upper lower u before
  after_shape : OrdinaryAxisTrainShape p upper lower v after
  before_readout : OrdinaryAxisReadout p upper lower u (ordinaryAxisPlacement p upper before)
  after_readout : OrdinaryAxisReadout p upper lower v (ordinaryAxisPlacement p upper after)
  player_column (changed : before.middle ≠ after.middle) : u.player.1.val = p.x upper.port
  middle_bounds : before.middle - 1 ≤ after.middle ∧ after.middle ≤ before.middle + 1
  middle_forward (moved : before.middle < after.middle) : (u.player.2.val : ℤ) = before.middle - 1
  middle_backward (moved : after.middle < before.middle) : (u.player.2.val : ℤ) = before.middle + before.middleLength

private theorem shape_of_line (p : Scales.Parameters) (upper lower : Endpoint)
    (initial : SignalState) (hpos : (ordinaryAxisTrainBlocks p upper lower initial).Positive)
    (T : LineState (Fin (ordinaryAxisTrainBlocks p upper lower initial).size) (p.W + 1) (p.H + 1) .south (p.x upper.port))
    (s : State (p.W + 1) (p.H + 1)) (hstate : T.state = BoxMask.keep s (ordinaryAxis p upper.port))
    (hgap : ((ordinaryAxisTrainBlocks p upper lower initial).atState hpos T).Gapped)
    (hs : (lineBoxes .south (p.x upper.port) T.state).image Direction.south.position =
      ((ordinaryAxisTrainBlocks p upper lower initial).atState hpos T).slots) :
    OrdinaryAxisTrainShape p upper lower s ((ordinaryAxisTrainBlocks p upper lower initial).atState hpos T) := by
  refine ⟨rfl, rfl, rfl, hgap, ?_⟩
  rw [hstate, BoxMask.lineBoxes_keep] at hs
  · exact hs
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
  {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
  (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)

local notation "I" => l.physicalInstance p hl hM ha initial target

include hu hlow hsuSide hslSide hport

include hl hM initial in
omit hsuSide hslSide hport in
private theorem shape_readout {s : State (p.W + 1) (p.H + 1)} {b : ThreeBlocks}
    (hs : OrdinaryAxisTrainShape p upper lower s b) :
    OrdinaryAxisReadout p upper lower s (ordinaryAxisPlacement p upper b) := by
  have hpos0 := l.ordinaryAxisTrainBlocks_positive p hl hM hu hlow initial
  have hpos : b.Positive := by
    change 0 < b.firstLength ∧ 0 < b.middleLength ∧ 0 < b.lastLength
    rw [hs.first_length, hs.middle_length, hs.last_length]
    exact hpos0
  exact hs.readout hpos

/-- A native ordinary shared-axis step lifts with the original three-train marks on both sides. -/
theorem physicalInstance_ordinaryAxis_train_marked_step {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    Nonempty (ThreeBlocks.MarkedStep (ordinaryAxisTrainBlocks p upper lower initial)
      (l.ordinaryAxisTrainBlocks_positive p hl hM hu hlow initial)
      (I).board none .south (p.x upper.port) (BoxMask.keep u (ordinaryAxis p upper.port)) (BoxMask.keep v (ordinaryAxis p upper.port))) := by
  let b := ordinaryAxisTrainBlocks p upper lower initial
  let c := ordinaryAxisTrainBlocks p upper lower target
  have hpre := l.physicalInstance_ordinaryAxis_admissible_prefix p hl hM ha initial target hu hlow hsuSide hslSide hport hsu
    ((Relation.ReflTransGen.single hm).trans hvt) ht
  have hpost := l.physicalInstance_ordinaryAxis_admissible_suffix p hl hM ha initial target hu hlow hsuSide hslSide hport (hsu.tail hm) hvt ht
  have hstep := BoxMask.keep_admissible (axis := .south) (lane := p.x upper.port) (ordinaryAxis_runClosed p upper.port)
    (fun _ hq => (Finset.mem_filter.mp hq).2.1) hm
    (l.physicalInstance_ordinaryAxis_inventory_step p hl hM ha initial target hu hlow hsuSide hslSide hport hsu hm hvt ht)
  exact b.admissible_step (l.ordinaryAxisTrainBlocks_positive p hl hM hu hlow initial)
    (l.ordinaryAxisTrainBlocks_gapped p hl hM hu hlow initial)
    c.first c.middle c.last (l.ordinaryAxisTrainBlocks_gapped p hl hM hu hlow target) hpre hstep hpost
    (l.physicalInstance_ordinaryAxis_train_initial_slots p hl hM ha initial target hu hlow hsuSide hslSide hport)
    (l.physicalInstance_ordinaryAxis_train_target_slots p hl hM ha initial target hu hlow hsuSide hslSide hport ht)

/-- Every real successful ordinary-axis step has its true middle-train motion and forcing player coordinates. -/
theorem physicalInstance_ordinaryAxis_train_motion {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    ∃ before after, OrdinaryAxisMotion p upper lower u v before after := by
  obtain ⟨m⟩ := l.physicalInstance_ordinaryAxis_train_marked_step p hl hM ha initial target hu hlow hsuSide hslSide hport hsu hm hvt ht
  have hbefore := shape_of_line p upper lower initial _ m.before u m.before_state m.before_gapped m.before_slots
  have hafter := shape_of_line p upper lower initial _ m.after v m.after_state m.after_gapped m.after_slots
  refine ⟨m.beforeBlocks, m.afterBlocks, hbefore, hafter,
    shape_readout l p hl hM initial hu hlow hbefore,
    shape_readout l p hl hM initial hu hlow hafter,
    ?_, ?_, m.middle_forward, m.middle_backward⟩
  · intro hchanged
    exact m.player_lane (Or.inr (Or.inl hchanged))
  · exact m.step.coordinate_bounds ⟨(ordinaryAxisTrainBlocks p upper lower initial).firstLength, by
      dsimp only [ThreeBlocks.size]
      have h := (l.ordinaryAxisTrainBlocks_positive p hl hM hu hlow initial).2.1
      omega⟩

end Solution

namespace OrdinaryAxisMotion

variable {p : Scales.Parameters} {upper lower : Endpoint} {u v : State (p.W + 1) (p.H + 1)}
  {before after : ThreeBlocks} (motion : OrdinaryAxisMotion p upper lower u v before after)

include motion

/-- The upper ordinary axis input stays failed while its actual pocket is inaccessible. -/
theorem upper_fault_preserved (hs : upper.side = .upper)
    (hbad : 2 ≤ (ordinaryAxisPlacement p upper before).parameter) (hout : u.player ∉ ordinaryPocket p upper) :
    2 ≤ (ordinaryAxisPlacement p upper after).parameter := by
  by_contra hrestore
  change 2 ≤ ((readDepth p upper.level : ℤ) + 4 - before.middle).toNat at hbad
  change ¬2 ≤ ((readDepth p upper.level : ℤ) + 4 - after.middle).toNat at hrestore
  have hbounds := motion.middle_bounds
  have hmoved : before.middle < after.middle := by omega
  have hp := motion.middle_forward hmoved
  have hx := motion.player_column (Ne.symm (ne_of_gt hmoved))
  have hy : u.player.2.val = readDepth p upper.level + 1 := by omega
  apply hout
  simp only [ordinaryPocket, Finset.mem_filter, Finset.mem_univ, true_and, hs, ite_true, hx,
    sub_self, ite_self, hy]
  exact Or.inl (Or.inr trivial)

/-- The complementary lower ordinary axis input stays failed while its actual pocket is inaccessible. -/
theorem lower_fault_preserved (hs : lower.side = .lower) (hp : lower.port = upper.port)
    (hbad : 2 ≤ (ordinaryAxisPlacement p upper before).lowerParameter) (hout : u.player ∉ ordinaryPocket p lower) :
    2 ≤ (ordinaryAxisPlacement p upper after).lowerParameter := by
  by_contra hrestore
  change 2 ≤ 3 - ((readDepth p upper.level : ℤ) + 4 - before.middle).toNat at hbad
  change ¬2 ≤ 3 - ((readDepth p upper.level : ℤ) + 4 - after.middle).toNat at hrestore
  have hbounds := motion.middle_bounds
  have hmoved : after.middle < before.middle := by omega
  have hforce := motion.middle_backward hmoved
  have hx := motion.player_column (Ne.symm (ne_of_lt hmoved))
  have hlen := motion.before_shape.middle_length
  have hDu := readDepth_add_lt_D p upper.level
  have hDl := readDepth_add_lt_D p lower.level
  have hH : p.H = 2 * p.D := rfl
  have hqy := u.player.2.isLt
  have hy : p.H - u.player.2.val = readDepth p lower.level + 1 := by omega
  have hx' : u.player.1.val = p.x lower.port := by simpa only [hp] using hx
  apply hout
  simp only [ordinaryPocket, Finset.mem_filter, Finset.mem_univ, true_and, hs, reduceCtorEq, ite_false,
    hx', sub_self, ite_self, hy]
  exact Or.inl (Or.inr trivial)

end OrdinaryAxisMotion
end PushPuzzle.PushS.PortLayout
