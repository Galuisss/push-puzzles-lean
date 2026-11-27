/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateTrainStep
import all PushS.PortGateTrains
import all PushS.PortLayoutCoordinates

/-! A current G or J can expand only from a player already inside that same actual gap. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- The actual working-row G interval recovered from the physical gate trains. -/
@[expose] def gateLeftGap (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind) (a : Shuttle.Placement) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  Finset.univ.filter fun q => q.2.val = p.H - readDepth p 1 ∧
    ((a).left : ℤ) - kind.kappa + 1 ≤ (q.1.val : ℤ) - p.x (g.left + 1) ∧ (q.1.val : ℤ) - p.x (g.left + 1) ≤ (a).short

/-- The actual working-row J interval recovered from the physical gate trains. -/
@[expose] def gateRightGap (p : Scales.Parameters) (g : Placement) (a : Shuttle.Placement) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  Finset.univ.filter fun q => q.2.val = p.H - readDepth p 1 ∧
    (a).short + 3 ≤ (q.1.val : ℤ) - p.x (g.left + 1) ∧ (q.1.val : ℤ) - p.x (g.left + 1) ≤ 13 - ((a).right : ℤ)

namespace GateTrainMotion

variable {p : Scales.Parameters} {g : Placement} {kind : Shuttle.Kind}
  {u v : State (p.W + 1) (p.H + 1)} {before after : ThreeBlocks}

local notation "a" => gateTrainPlacement p g before
local notation "c" => gateTrainPlacement p g after

private theorem player_in_right (motion : GateTrainMotion p g kind u v before after)
    (hshape : g.right = g.left + 2) (hrow : u.player.2.val = p.H - readDepth p 1)
    (hx : (u.player.1.val : ℤ) - p.x (g.left + 1) = (a).short + 3 ∨
      (u.player.1.val : ℤ) - p.x (g.left + 1) = 13 - ((a).right : ℤ)) : u.player ∈ gateRightGap p g a := by
  have hg := motion.before_shape.placement_gapped hshape
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hrow, ?_⟩
  rcases hx with hx | hx <;> omega

private theorem player_in_left (motion : GateTrainMotion p g kind u v before after)
    (hshape : g.right = g.left + 2) (hrow : u.player.2.val = p.H - readDepth p 1)
    (hx : (u.player.1.val : ℤ) - p.x (g.left + 1) = ((a).left : ℤ) - kind.kappa + 1 ∨
      (u.player.1.val : ℤ) - p.x (g.left + 1) = (a).short) : u.player ∈ gateLeftGap p g kind a := by
  have hg := motion.before_shape.placement_gapped hshape
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hrow, ?_⟩
  rcases hx with hx | hx <;> omega

/-- Outside J, the short train and right outer count can only shrink the current J interval. -/
theorem right_parameters_mono (motion : GateTrainMotion p g kind u v before after)
    (hshape : g.right = g.left + 2) (hout : u.player ∉ gateRightGap p g a) :
    (a).short ≤ (c).short ∧ (a).right ≤ (c).right := by
  have hb := motion.before_shape.placement_coordinates
  have hc := motion.after_shape.placement_coordinates
  have hshortB : (a).short = before.middle - (p.x (g.left + 1) : ℤ) - 1 := rfl
  have hshortC : (c).short = after.middle - (p.x (g.left + 1) : ℤ) - 1 := rfl
  constructor
  · by_contra hbad
    have hm : after.middle < before.middle := by omega
    have hx := motion.middle_backward hm
    have hlen := motion.before_shape.middle_length
    have hy := motion.player_row (Or.inr (Or.inl (ne_of_gt hm)))
    exact hout (motion.player_in_right hshape hy (Or.inl (by omega)))
  · by_contra hbad
    have hlastB := motion.before_shape.last_length
    have hlastC := motion.after_shape.last_length
    have hm : before.last < after.last := by omega
    have hx := motion.last_forward hm
    have hy := motion.player_row (Or.inr (Or.inr (ne_of_lt hm)))
    have hr : p.x g.right = p.x (g.left + 1) + p.D := by
      simpa only [hshape, Nat.add_assoc] using x_succ_eq p (g.left + 1)
    have hD := readDepth_readLength_margin p 0 0
    exact hout (motion.player_in_right hshape hy (Or.inr (by omega)))

/-- Outside G, the short train and left outer count can only shrink the current G interval. -/
theorem left_parameters_mono (motion : GateTrainMotion p g kind u v before after)
    (hshape : g.right = g.left + 2) (hout : u.player ∉ gateLeftGap p g kind a) :
    (c).short ≤ (a).short ∧ (a).left ≤ (c).left := by
  have hb := motion.before_shape.placement_coordinates
  have hc := motion.after_shape.placement_coordinates
  have hshortB : (a).short = before.middle - (p.x (g.left + 1) : ℤ) - 1 := rfl
  have hshortC : (c).short = after.middle - (p.x (g.left + 1) : ℤ) - 1 := rfl
  constructor
  · by_contra hbad
    have hm : before.middle < after.middle := by omega
    have hx := motion.middle_forward hm
    have hy := motion.player_row (Or.inr (Or.inl (ne_of_lt hm)))
    exact hout (motion.player_in_left hshape hy (Or.inr (by omega)))
  · by_contra hbad
    have hm : after.first < before.first := by omega
    have hx := motion.first_backward hm
    have hy := motion.player_row (Or.inl (ne_of_gt hm))
    have hlen := motion.before_shape.first_length
    have hmid := x_succ_eq p g.left
    have hD := readDepth_readLength_margin p 0 0
    have hk : (kind.kappa.toNat : ℤ) = kind.kappa := by cases kind <;> decide +kernel
    have hk4 : kind.kappa.toNat ≤ 4 := by cases kind <;> decide +kernel
    exact hout (motion.player_in_left hshape hy (Or.inl (by omega)))

/-- A real step from outside J leaves a subset of its previous current J interval. -/
theorem right_gap_subset (motion : GateTrainMotion p g kind u v before after)
    (hshape : g.right = g.left + 2) (hout : u.player ∉ gateRightGap p g a) :
    gateRightGap p g c ⊆ gateRightGap p g a := by
  have hm := motion.right_parameters_mono hshape hout
  intro q hq
  obtain ⟨_, hy, hlo, hhi⟩ := Finset.mem_filter.mp hq
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hy, ?_⟩
  change (c).short + 3 ≤ (q.1.val : ℤ) - p.x (g.left + 1) at hlo
  change (q.1.val : ℤ) - p.x (g.left + 1) ≤ 13 - ((c).right : ℤ) at hhi
  omega

/-- A real step from outside G leaves a subset of its previous current G interval. -/
theorem left_gap_subset (motion : GateTrainMotion p g kind u v before after)
    (hshape : g.right = g.left + 2) (hout : u.player ∉ gateLeftGap p g kind a) :
    gateLeftGap p g kind c ⊆ gateLeftGap p g kind a := by
  have hm := motion.left_parameters_mono hshape hout
  intro q hq
  obtain ⟨_, hy, hlo, hhi⟩ := Finset.mem_filter.mp hq
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hy, ?_⟩
  change ((c).left : ℤ) - kind.kappa + 1 ≤ (q.1.val : ℤ) - p.x (g.left + 1) at hlo
  change (q.1.val : ℤ) - p.x (g.left + 1) ≤ (c).short at hhi
  omega

/-- A relay fault's two defining thresholds persist while the player stays outside its current J. -/
theorem relay_fault_preserved (motion : GateTrainMotion p g kind u v before after)
    (hshape : g.right = g.left + 2) (hout : u.player ∉ gateRightGap p g a)
    (hshort : 6 ≤ (a).short) (hright : 2 ≤ (a).right) : 6 ≤ (c).short ∧ 2 ≤ (c).right := by
  have hm := motion.right_parameters_mono hshape hout
  omega

end GateTrainMotion

/-- In a relay fault, the complete actual J lies in the three columns 9 through 11. -/
theorem gateRightGap_relay_bounds (p : Scales.Parameters) (g : Placement) (a : Shuttle.Placement)
    (hshort : 6 ≤ (a).short) (hright : 2 ≤ (a).right) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ gateRightGap p g a) : 9 ≤ (q.1.val : ℤ) - p.x (g.left + 1) ∧
      (q.1.val : ℤ) - p.x (g.left + 1) ≤ 11 := by
  obtain ⟨_, _, hlo, hhi⟩ := Finset.mem_filter.mp hq
  change (a).short + 3 ≤ (q.1.val : ℤ) - p.x (g.left + 1) at hlo
  change (q.1.val : ℤ) - p.x (g.left + 1) ≤ 13 - ((a).right : ℤ) at hhi
  omega

end PushPuzzle.PushS.PortLayout
