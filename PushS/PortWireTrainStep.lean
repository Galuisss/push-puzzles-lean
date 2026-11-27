/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.IntervalStep
public import PushS.PortOrdinaryFailure
import all PushS.PortWireTrains

/-! A genuine ordinary WIRE step with its entire single train and actual player forcing sides. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- The same actual WIRE train, before and after one real physical step. -/
structure WireTrainStep (p : Scales.Parameters) (g : Placement) (B : Board (p.W + 1) (p.H + 1))
    (u v : State (p.W + 1) (p.H + 1)) where
  first : ℤ
  next : ℤ
  source_shape : WireTrainShape p g u first
  target_shape : WireTrainShape p g v next
  marked : IntervalMarkedStep B none .east
    (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level) (wireTrainLength p g)
    (BoxMask.keep u (wireOpenRail p g)) (BoxMask.keep v (wireOpenRail p g)) first next

/-- Every next step of an actual successful WIRE trajectory has its complete consistent train marks. -/
theorem physicalInstance_wire_train_step (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hm : Step (l.physicalInstance p hl hM ha initial target).board none u v)
    (hvt : Reachable (l.physicalInstance p hl hM ha initial target).board none v t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Nonempty (WireTrainStep p g (l.physicalInstance p hl hM ha initial target).board u v) := by
  obtain ⟨first, hs⟩ := l.physicalInstance_wire_train_shape p hl hM ha initial target hg hw hsu
    ((Relation.ReflTransGen.single hm).trans hvt) ht
  obtain ⟨next, hv⟩ := l.physicalInstance_wire_train_shape p hl hM ha initial target hg hw (hsu.tail hm) hvt ht
  have hon (q : Cell (p.W + 1) (p.H + 1)) (hq : q ∈ wireOpenRail p g) :
      Direction.east.lane q = (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level) :=
    (Finset.mem_filter.mp hq).2.1
  have hstep := BoxMask.keep_admissible (wireOpenRail_runClosed p g) hon hm
    (l.physicalInstance_wire_inventory_step p hl hM ha initial target hg hw hsu hm hvt ht)
  have sourceSlots : (lineBoxes .east (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
      (BoxMask.keep u (wireOpenRail p g))).image Direction.east.position = Finset.Ico first (first + wireTrainLength p g) := by
    rw [BoxMask.lineBoxes_keep hon]
    exact hs.slots
  have targetSlots : (lineBoxes .east (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
      (BoxMask.keep v (wireOpenRail p g))).image Direction.east.position = Finset.Ico next (next + wireTrainLength p g) := by
    rw [BoxMask.lineBoxes_keep hon]
    exact hv.slots
  obtain ⟨marked⟩ := interval_marked_step (l.wireTrainLength_positive p hl hg hw) hstep sourceSlots targetSlots
  exact ⟨⟨first, next, hs, hv, marked⟩⟩

namespace WireTrainStep

variable {p : Scales.Parameters} {g : Placement} {B : Board (p.W + 1) (p.H + 1)}
  {u v : State (p.W + 1) (p.H + 1)} (step : WireTrainStep p g B u v)

include step

/-- The actual WIRE train's first coordinate changes by at most one. -/
theorem start_bounds : step.first - 1 ≤ step.next ∧ step.next ≤ step.first + 1 := step.marked.start_bounds

/-- Increasing the actual WIRE train requires its true player just before the first box. -/
theorem force_increase (hi : step.first < step.next) :
    (u.player.1.val : ℤ) = step.first - 1 ∧
      u.player.2.val = (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level) :=
  step.marked.force_increase hi

/-- Decreasing the actual WIRE train requires its true player just after the last box. -/
theorem force_decrease (hi : step.next < step.first) :
    (u.player.1.val : ℤ) = step.first + wireTrainLength p g ∧
      u.player.2.val = (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level) :=
  step.marked.force_decrease hi

/-- A small left endpoint gap cannot grow while the real player is outside its actual ordinary pocket. -/
theorem left_gap_no_growth (hsmall : step.first ≤ (p.x g.left : ℤ) + 2)
    (hout : u.player ∉ ordinaryPocket p ⟨g.side, g.left, true, g.level, g.internal⟩) : step.next ≤ step.first := by
  by_contra hi
  have hforce := step.force_increase (by omega)
  have hfit := step.source_shape.fits step.marked.length_pos
  apply hout
  simp only [ordinaryPocket, Finset.mem_filter, Finset.mem_univ, true_and, ite_true]
  have hH := readDepth_add_lt_H p g.level
  have hpy := u.player.2.isLt
  cases hs : g.side <;> simp only [hs, reduceCtorEq, ite_false, ite_true] at hforce ⊢ <;> omega

/-- A small right endpoint gap cannot grow while the real player is outside its actual ordinary pocket. -/
theorem right_gap_no_growth (hsmall : (p.x g.right : ℤ) - 1 ≤ step.first + wireTrainLength p g)
    (hout : u.player ∉ ordinaryPocket p ⟨g.side, g.right, false, g.level, g.internal⟩) : step.first ≤ step.next := by
  by_contra hi
  have hforce := step.force_decrease (by omega)
  have hfit := step.source_shape.fits step.marked.length_pos
  apply hout
  simp only [ordinaryPocket, Finset.mem_filter, Finset.mem_univ, true_and, Bool.false_eq_true, ite_false]
  have hH := readDepth_add_lt_H p g.level
  have hpy := u.player.2.isLt
  cases hs : g.side <;> simp only [hs, reduceCtorEq, ite_false, ite_true] at hforce ⊢ <;> omega

/-- A failed left WIRE horizontal supply persists through the actual step while its pocket is inaccessible. -/
theorem left_fault_preserved (hsmall : (step.first - (p.x g.left : ℤ) - 1).toNat ≤ 1)
    (hout : u.player ∉ ordinaryPocket p ⟨g.side, g.left, true, g.level, g.internal⟩) :
    (step.next - (p.x g.left : ℤ) - 1).toNat ≤ 1 := by
  have hfit := step.source_shape.fits step.marked.length_pos
  have hnext := step.left_gap_no_growth (by omega) hout
  omega

/-- A failed right WIRE horizontal supply persists through the actual step while its pocket is inaccessible. -/
theorem right_fault_preserved (hsmall : ((p.x g.right : ℤ) - step.first - wireTrainLength p g).toNat ≤ 1)
    (hout : u.player ∉ ordinaryPocket p ⟨g.side, g.right, false, g.level, g.internal⟩) :
    ((p.x g.right : ℤ) - step.next - wireTrainLength p g).toNat ≤ 1 := by
  have hfit := step.source_shape.fits step.marked.length_pos
  have hnext := step.right_gap_no_growth (by omega) hout
  omega

end WireTrainStep
end PushPuzzle.PushS.PortLayout
