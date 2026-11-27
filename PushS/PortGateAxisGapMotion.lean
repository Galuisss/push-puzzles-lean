/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateAxisTrainStep
import all PushS.PortGateAxisTrainReadout
import all PushS.PortLayoutCoordinates

/-! The lower middle-axis near interval expands only from a player already in that same interval. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- The closed middle-axis near interval, including the lower work-row junction. -/
@[expose] def gateAxisNear (p : Scales.Parameters) (g : Placement) (parameter : ℕ) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  Finset.univ.filter fun q => q.1.val = p.x (g.left + 1) ∧
    p.H - readDepth p 1 - parameter ≤ q.2.val ∧ q.2.val ≤ p.H - readDepth p 1

namespace GateAxisTrainMotion

variable {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
  {u v : State (p.W + 1) (p.H + 1)} {before after : TwoBlocks}

local notation "a" => gateAxisPlacement p upper before
local notation "c" => gateAxisPlacement p upper after

/-- The core's near-axis hole count cannot increase from a player outside its closed current near interval. -/
theorem core_parameter_mono (motion : GateAxisTrainMotion p g upper u v before after)
    (hout : u.player ∉ gateAxisNear p g (a).parameter) : (c).parameter ≤ (a).parameter := by
  have hb := motion.before_shape.placement_coordinates motion.before_positive
  have hc := motion.after_shape.placement_coordinates motion.after_positive
  by_contra hbad
  have hm : after.last < before.last := by omega
  have hy := motion.last_backward hm
  have hx := motion.player_column (Or.inr (ne_of_gt hm))
  have hlen := motion.before_shape.last_length
  have hDu := readDepth_add_lt_D p upper.level
  have hD1 := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  apply hout
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, hx, by omega, by omega⟩

/-- The actual closed core near interval only shrinks under a move from outside it. -/
theorem core_near_subset (motion : GateAxisTrainMotion p g upper u v before after)
    (hout : u.player ∉ gateAxisNear p g (a).parameter) :
    gateAxisNear p g (c).parameter ⊆ gateAxisNear p g (a).parameter := by
  have hm := motion.core_parameter_mono hout
  intro q hq
  obtain ⟨_, hx, hlo, hhi⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, by omega, hhi⟩

/-- A lost middle-axis supply remains lost while the player stays outside its current closed near interval. -/
theorem core_fault_preserved (motion : GateAxisTrainMotion p g upper u v before after)
    (hout : u.player ∉ gateAxisNear p g (a).parameter) (hbad : (a).parameter ≤ 1) : (c).parameter ≤ 1 := by
  exact (motion.core_parameter_mono hout).trans hbad

end GateAxisTrainMotion
end PushPuzzle.PushS.PortLayout
