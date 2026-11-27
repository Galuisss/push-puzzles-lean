/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateTrainStep
public import PushS.PortOrdinaryFailure

/-! The actual gate's two ordinary endpoint gaps preserve W failures from outside their pockets. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

namespace GateTrainMotion

variable {p : Scales.Parameters} {g : Placement} {kind : Shuttle.Kind}
  {u v : State (p.W + 1) (p.H + 1)} {before after : ThreeBlocks}
  (motion : GateTrainMotion p g kind u v before after)

include motion

/-- The left ordinary gate endpoint keeps its failed horizontal supply while its pocket is inaccessible. -/
theorem left_wire_fault_preserved (hside : g.side = .lower) (hlevel : g.level = 1)
    (hbad : (gateTrainPlacement p g before).left ≤ 1)
    (hout : u.player ∉ ordinaryPocket p ⟨g.side, g.left, true, g.level, g.internal⟩) :
    (gateTrainPlacement p g after).left ≤ 1 := by
  by_contra hrestore
  have hbefore := motion.before_shape.placement_coordinates
  have hafter := motion.after_shape.placement_coordinates
  have hmoved : before.first < after.first := by omega
  have hp := motion.first_forward hmoved
  have hy := motion.player_row (Or.inl (ne_of_lt hmoved))
  have hfit := motion.before_shape.fits
  have hH := readDepth_add_lt_H p 1
  have hqy := u.player.2.isLt
  apply hout
  simp only [ordinaryPocket, Finset.mem_filter, Finset.mem_univ, true_and, hside, hlevel,
    reduceCtorEq, ite_false, ite_true]
  omega

/-- The right ordinary gate endpoint keeps its failed horizontal supply while its pocket is inaccessible. -/
theorem right_wire_fault_preserved (hside : g.side = .lower) (hlevel : g.level = 1)
    (hbad : (gateTrainPlacement p g before).right ≤ 1)
    (hout : u.player ∉ ordinaryPocket p ⟨g.side, g.right, false, g.level, g.internal + 2⟩) :
    (gateTrainPlacement p g after).right ≤ 1 := by
  by_contra hrestore
  have hbefore := motion.before_shape.placement_coordinates
  have hafter := motion.after_shape.placement_coordinates
  have hbeforeLen := motion.before_shape.last_length
  have hafterLen := motion.after_shape.last_length
  have hmoved : after.last < before.last := by omega
  have hp := motion.last_backward hmoved
  have hy := motion.player_row (Or.inr (Or.inr (Ne.symm (ne_of_lt hmoved))))
  have hfit := motion.before_shape.fits
  have hH := readDepth_add_lt_H p 1
  have hqy := u.player.2.isLt
  apply hout
  simp only [ordinaryPocket, Finset.mem_filter, Finset.mem_univ, true_and, hside, hlevel,
    reduceCtorEq, Bool.false_eq_true, ite_false]
  omega

end GateTrainMotion
end PushPuzzle.PushS.PortLayout
