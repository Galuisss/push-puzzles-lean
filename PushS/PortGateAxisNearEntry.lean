/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateAxisGapMotion
public import PushS.PortGateGapMotion
public import PushS.PortGatePrivateEntry
import all PushS.PortGatePrivateEntry
import all PushS.PortGatePrivateWalk
import all PushS.PortGateBottomWall
import all PushS.PortGatePageWindow
import all PushS.PortSignalLocality
import all PushS.PortCoreCrossing
import all PushS.PortStreetSeparation
import all PushS.PortSegments

/-! Actual entrances to the closed middle-axis near interval, including its work-row junction. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

private theorem left_bottom_player_impossible {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) (hx : u.player.1.val + 1 = p.x middle)
    (hy : u.player.2.val = p.H - (readDepth p 1 + 2)) : False := by
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have hw : u.player ∈ gatePageWindow p middle := by
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    simp only [Nat.dist]
    omega
  have hinitial : u.player ∈ (I).initial.boxes := by
    by_contra hb
    have hh := (mem_holes u.player).mpr hb
    change u.player ∈ (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial))ᶜᶜ at hh
    rw [compl_compl] at hh
    exact bottom_source_clear l p initial (Or.inr ⟨hy, Or.inl (by omega)⟩)
      (l.encodedSegments_gatePageWindow p hl hM ha initial hi hw hh)
  have hblock := private_bottom l p hl hM ha hi (Or.inl (show u.player.1.val = p.x middle - 1 by omega)) hy
  have hpaths := l.physicalInstance_gate_private_avoiding_prefix p hl hM ha initial target hi hsu hut ht
  exact (hsu.valid (I).initial_valid).2.2 (avoiding_box hpaths hblock hinitial)

/-- A real entry into the current closed axis-near interval comes from G or, for at least two near holes, the private branch. -/
theorem physicalInstance_gate_axis_near_entry {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {upper : Endpoint} {axisPlacement : GateAxisPlacement}
    (haxis : GateAxisReadout p g upper u axisPlacement)
    {b : ThreeBlocks} (hs : GateTrainShape p g kind u b)
    (hleft : -1 ≤ ((gateTrainPlacement p g b).left : ℤ) - kind.kappa + 1)
    (hout : u.player ∉ gateAxisNear p g axisPlacement.parameter)
    (hin : v.player ∈ gateAxisNear p g axisPlacement.parameter) :
    u.player ∈ gateLeftGap p g kind (gateTrainPlacement p g b) ∨
      (2 ≤ axisPlacement.parameter ∧ u.player ∈ gatePrivateCells p (g.left + 1)) := by
  obtain ⟨_, htx, htlo, hthi⟩ := Finset.mem_filter.mp hin
  have hut := (Relation.ReflTransGen.single hm).trans hvt
  have hi := center_of_gate l (placement_gate_mem l hg hk)
  have hparam := haxis.parameter_le
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have hshape := (placement_gate_shape l hg hk).2
  have hgap := hs.placement_gapped hshape
  have horizontal (hx : u.player.1.val + 1 = p.x (g.left + 1) ∨ u.player.1.val = p.x (g.left + 1) + 1)
      (hy : u.player.2.val = v.player.2.val) :
      u.player ∈ gateLeftGap p g kind (gateTrainPlacement p g b) ∨
        (2 ≤ axisPlacement.parameter ∧ u.player ∈ gatePrivateCells p (g.left + 1)) := by
    have hxe := x_even p (g.left + 1)
    have hYe := readDepth_even p 1
    have hHe := H_even p
    have hxodd : u.player.1.val % 2 = 1 := by rcases hx with h | h <;> omega
    have hstreet := l.physicalInstance_player_on_streets p hl hM ha initial target hsu hut ht
    have hrowEven : u.player.2.val % 2 = 0 := by
      rcases hstreet with hc | hr
      · have he := l.streetColumnSet_even p hc
        omega
      · exact l.workingRowSet_even p hr
    have hrows : u.player.2.val = p.H - readDepth p 1 ∨ u.player.2.val = p.H - (readDepth p 1 + 2) := by omega
    rcases hrows with hrow | hrow
    · have hxrange : -2 ≤ (u.player.1.val : ℤ) - p.x (g.left + 1) ∧ (u.player.1.val : ℤ) - p.x (g.left + 1) ≤ 12 := by
        rcases hx with h | h <;> omega
      have hh : u.player ∈ holes u := (mem_holes _).mpr hm.choose_spec.valid_source.2.2
      rcases (hs.core_hole hshape hrow hxrange).mp hh with hG | hJ
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrow, hG⟩)
      · have hstart := hJ.1
        rcases hx with h | h <;> omega
    · have htwo : 2 ≤ axisPlacement.parameter := by omega
      rcases hx with hleftCol | hrightCol
      · exact False.elim (left_bottom_player_impossible l p hl hM ha initial target hi hsu hut ht hleftCol hrow)
      · exact Or.inr ⟨htwo, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hrow, by omega, by omega⟩⟩⟩
  obtain ⟨d, hmove⟩ := hm
  have hadj := players_adjacent hmove
  have hh : u.player ∈ holes u := (mem_holes _).mpr hmove.valid_source.2.2
  cases d with
  | north =>
    have hx : u.player.1.val = p.x (g.left + 1) := (congrArg Fin.val hadj.1).symm.trans htx
    have habove : u.player.2.val = p.H - readDepth p 1 + 1 := by
      by_contra hnot
      apply hout
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, by have hy := hadj.2; omega, by have hy := hadj.2; omega⟩
    have hback : u.player.2.val = p.H - (readDepth p 1 - 1) := by omega
    have hrod := l.gateHalfRods_back_mem p hi (Or.inl hx) hback
    have hblock := l.gatePrivateBlockers_back_mem p hl hM ha hi (Or.inl hx) hback
    have hbox := l.gateHalfRods_initial_full p hl hM ha initial target hrod
    have hpaths := l.physicalInstance_gate_private_avoiding_prefix p hl hM ha initial target hi hsu hut ht
    exact False.elim (hmove.valid_source.2.2 (avoiding_box hpaths hblock hbox))
  | south =>
    have hx : u.player.1.val = p.x (g.left + 1) := (congrArg Fin.val hadj.1).symm.trans htx
    have hbelow : u.player.2.val < p.H - readDepth p 1 - axisPlacement.parameter := by
      by_contra hnot
      apply hout
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, by omega, by have hy := hadj.2; omega⟩
    have hhalf : p.D ≤ u.player.2.val ∧ u.player.2.val < p.H - readDepth p 1 := by have hy := hadj.2; omega
    have hhole := (haxis.core_holes u.player hx hhalf).mp hh
    omega
  | east =>
    exact horizontal (Or.inl (by have hx := hadj.1; omega))
      ((congrArg Fin.val hadj.2).symm)
  | west =>
    exact horizontal (Or.inr (by have hx := hadj.1; omega)) ((congrArg Fin.val hadj.2).symm)

end Solution
end PushPuzzle.PushS.PortLayout
