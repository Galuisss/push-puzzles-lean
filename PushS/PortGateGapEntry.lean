/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateGapMotion
public import PushS.PortGatePlayerColumns
public import PushS.PortGatePrivateEntry
import all PushS.PortGatePrivateEntry
import all PushS.PortSignalLocality
import all PushS.PortCoreCrossing
import all PushS.PortSegments

/-! The only real entrances to a low gate G are its private cap and its lower adjacent axis cell. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

private theorem horizontal_excluded {p : Scales.Parameters} {g : Placement} {kind : Shuttle.Kind}
    {u : State (p.W + 1) (p.H + 1)} {b : ThreeBlocks} (hs : GateTrainShape p g kind u b)
    (hshape : g.right = g.left + 2)
    (hleft : -1 ≤ ((gateTrainPlacement p g b).left : ℤ) - kind.kappa + 1)
    (hshort : (gateTrainPlacement p g b).short ≤ 5) {q r : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∉ gateLeftGap p g kind (gateTrainPlacement p g b))
    (hr : r ∈ gateLeftGap p g kind (gateTrainPlacement p g b))
    (hy : q.2.val = p.H - readDepth p 1) (hdx : q.1.val + 1 = r.1.val ∨ r.1.val + 1 = q.1.val)
    (hhole : q ∈ holes u) : False := by
  obtain ⟨_, _, hrleft, hrright⟩ := Finset.mem_filter.mp hr
  change ((gateTrainPlacement p g b).left : ℤ) - kind.kappa + 1 ≤ (r.1.val : ℤ) - p.x (g.left + 1) at hrleft
  change (r.1.val : ℤ) - p.x (g.left + 1) ≤ (gateTrainPlacement p g b).short at hrright
  have hrange : -2 ≤ (q.1.val : ℤ) - p.x (g.left + 1) ∧ (q.1.val : ℤ) - p.x (g.left + 1) ≤ 12 := by
    rcases hdx with h | h <;> omega
  rcases (hs.core_hole hshape hy hrange).mp hhole with hG | hJ
  · exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, hG⟩)
  · have hJleft := hJ.1
    rcases hdx with h | h <;> omega

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- A real step from outside the current low G enters it only from the private branch or the lower axis neighbour. -/
theorem physicalInstance_gate_left_gap_entry {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {b : ThreeBlocks} (hs : GateTrainShape p g kind u b)
    (hleft : -1 ≤ ((gateTrainPlacement p g b).left : ℤ) - kind.kappa + 1)
    (hshort : (gateTrainPlacement p g b).short ≤ 5)
    (hout : u.player ∉ gateLeftGap p g kind (gateTrainPlacement p g b))
    (hin : v.player ∈ gateLeftGap p g kind (gateTrainPlacement p g b)) :
    u.player ∈ gatePrivateCells p (g.left + 1) ∨
      (u.player.1.val = p.x (g.left + 1) ∧ u.player.2.val + 1 = p.H - readDepth p 1) := by
  obtain ⟨_, hy, hlo, hhi⟩ := Finset.mem_filter.mp hin
  change ((gateTrainPlacement p g b).left : ℤ) - kind.kappa + 1 ≤ (v.player.1.val : ℤ) - p.x (g.left + 1) at hlo
  change (v.player.1.val : ℤ) - p.x (g.left + 1) ≤ (gateTrainPlacement p g b).short at hhi
  have hut := (Relation.ReflTransGen.single hm).trans hvt
  have hi := center_of_gate l (placement_gate_mem l hg hk)
  have vertical (hrow : u.player.2.val + 1 = p.H - readDepth p 1 ∨ u.player.2.val = p.H - readDepth p 1 + 1)
      (hrange : -1 ≤ (u.player.1.val : ℤ) - p.x (g.left + 1) ∧ (u.player.1.val : ℤ) - p.x (g.left + 1) ≤ 5) :
      u.player ∈ gatePrivateCells p (g.left + 1) ∨
        (u.player.1.val = p.x (g.left + 1) ∧ u.player.2.val + 1 = p.H - readDepth p 1) := by
    have hc := l.physicalInstance_gate_player_adjacent_columns p hl hM ha initial target hg hk hsu hut ht hrow
      (by simp only [Nat.dist]; omega)
    have hcx : (coordinates p).x = p.x := rfl
    have hx0 := readLength_add_lt_x p (g.left + 1) 0
    simp only [gateSpecialColumns, specialColumns, hcx, List.mem_cons, List.not_mem_nil, or_false] at hc
    have hcolumn : u.player.1.val = p.x (g.left + 1) ∨ u.player.1.val = p.x (g.left + 1) + 4 := by omega
    have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
    have hH := readDepth_add_lt_H p 1
    rcases hrow with hbelow | habove
    · rcases hcolumn with hx | hx
      · exact Or.inr ⟨hx, hbelow⟩
      · left
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, Or.inl ⟨hx, by omega⟩⟩
    · have hback : u.player.2.val = p.H - (readDepth p 1 - 1) := by omega
      have hrod := l.gateHalfRods_back_mem p hi hcolumn hback
      have hblock := l.gatePrivateBlockers_back_mem p hl hM ha hi hcolumn hback
      have hbox := l.gateHalfRods_initial_full p hl hM ha initial target hrod
      have hpaths := l.physicalInstance_gate_private_avoiding_prefix p hl hM ha initial target hi hsu hut ht
      exact False.elim (hm.choose_spec.valid_source.2.2 (avoiding_box hpaths hblock hbox))
  obtain ⟨d, hmove⟩ := hm
  have hadj := players_adjacent hmove
  have hhole : u.player ∈ holes u := (mem_holes _).mpr hmove.valid_source.2.2
  have hshape := (placement_gate_shape l hg hk).2
  cases d with
  | north =>
    have hx := congrArg Fin.val hadj.1
    have hyy := hadj.2
    exact vertical (Or.inr (by omega)) ⟨by omega, by omega⟩
  | south =>
    have hx := congrArg Fin.val hadj.1
    have hyy := hadj.2
    exact vertical (Or.inl (by omega)) ⟨by omega, by omega⟩
  | east =>
    have hyy := congrArg Fin.val hadj.2
    exact False.elim (horizontal_excluded hs hshape hleft hshort hout hin (by omega) (Or.inl hadj.1.symm) hhole)
  | west =>
    have hyy := congrArg Fin.val hadj.2
    exact False.elim (horizontal_excluded hs hshape hleft hshort hout hin (by omega) (Or.inr hadj.1) hhole)

end Solution
end PushPuzzle.PushS.PortLayout
