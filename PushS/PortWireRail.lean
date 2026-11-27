/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortWireCrossings
public import PushS.InventoryEmpty
import all PushS.PortWireMacro
import all PushS.PortWireIndexing
import all PushS.PortEndpointCounts
import all PushS.PortSegmentInventory
import all PushS.PortSegments

/-! The actual open horizontal rail of an ordinary WIRE has three canonical holes. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The work-row interval strictly between the two original axes of a WIRE. -/
@[expose] def wireOpenRail (p : Scales.Parameters) (g : Placement) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  Finset.univ.filter fun q =>
    q.2.val = (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level) ∧
      p.x g.left < q.1.val ∧ q.1.val < p.x g.right

/-- The two horizontal receiving slots of an ordinary WIRE. -/
def wireNearSegments (p : Scales.Parameters) (state : SignalState) (g : Placement) :
    List Segment :=
  (endpointSegments (coordinates p) state (wireLeft g)).drop 1 ++
    (endpointSegments (coordinates p) state (wireRight g)).drop 1

private theorem wire_near_mem (p : Scales.Parameters) (state : SignalState)
    (g : Placement) (q : ℕ × ℕ) :
    q ∈ pointHoles (wireNearSegments p state g) ↔
      q.2 = (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level) ∧
      ((p.x g.left + 1 ≤ q.1 ∧ q.1 ≤ p.x g.left + 1 + (state.internal.getD g.internal false).toNat) ∨
        (p.x g.right - (1 + (!(state.internal.getD g.internal false)).toNat) ≤ q.1 ∧
          q.1 ≤ p.x g.right - 1)) := by
  have hx := readLength_add_lt_x p g.right 0
  unfold wireNearSegments
  dsimp only [wireLeft, wireRight]
  rw [pointHoles_append]
  simp only [endpointSegments, List.drop_succ_cons, List.drop_zero, Finset.mem_union]
  rw [horizontal_mem, horizontal_mem]
  simp only [Bool.false_eq_true, ite_false, ite_true, inward, onSide]
  change ((q.2 = _ ∧ min (p.x g.left + 1) (p.x g.left + (1 + (state.internal.getD g.internal false).toNat)) ≤ q.1 ∧
      q.1 ≤ max (p.x g.left + 1) (p.x g.left + (1 + (state.internal.getD g.internal false).toNat))) ∨
    (q.2 = _ ∧ min (p.x g.right - 1) (p.x g.right - (1 + (!(state.internal.getD g.internal false)).toNat)) ≤ q.1 ∧
      q.1 ≤ max (p.x g.right - 1) (p.x g.right - (1 + (!(state.internal.getD g.internal false)).toNat)))) ↔ _
  have hb := Bool.toNat_le (state.internal.getD g.internal false)
  have hn := Bool.toNat_le (!(state.internal.getD g.internal false))
  have hrow : (if g.side = .upper then (coordinates p).depth g.level
      else (coordinates p).H - (coordinates p).depth g.level) =
      (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level) := rfl
  rw [hrow]
  omega

private theorem wire_near_subset_rail (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (state : SignalState) {g : Placement}
    (hg : g ∈ placements l) (hw : g.gate = none) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1) (wireNearSegments p state g) ⊆ wireOpenRail p g := by
  have hports := wire_ports l hl hg hw
  have hgap := axis_spacing p hports.1
  have hd := p.outer_distance
  have hb := Bool.toNat_le (state.internal.getD g.internal false)
  have hn := Bool.toNat_le (!(state.internal.getD g.internal false))
  intro q hq
  have hm := (wire_near_mem p state g _).mp ((finite_mem p _ q).mp hq)
  simp only [wireOpenRail, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hm.1, by omega, by omega⟩

private theorem wire_pair_rail_near (p : Scales.Parameters) (state : SignalState)
    (g : Placement) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (endpointSegments (coordinates p) state (wireLeft g) ++
        endpointSegments (coordinates p) state (wireRight g)))
    (hr : q ∈ wireOpenRail p g) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (wireNearSegments p state g) := by
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  have hr := (Finset.mem_filter.mp hr).2
  apply (SegmentRecipe.mem_holes _ q).mpr
  rcases List.mem_append.mp hs with hs | hs
  · dsimp only [endpointSegments] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · have hx := (vertical_coordinates hc).1
      change q.1.val = p.x g.left at hx
      omega
    · exact ⟨_, List.mem_append_left _ (by simp [endpointSegments]), hc⟩
  · dsimp only [endpointSegments] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · have hx := (vertical_coordinates hc).1
      change q.1.val = p.x g.right at hx
      omega
    · exact ⟨_, List.mem_append_right _ (by simp [endpointSegments]), hc⟩

/-- The complete marked board contributes precisely the two receiving slots to an open WIRE. -/
theorem encodedSegments_wireOpenRail (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) ∩ wireOpenRail p g =
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (wireNearSegments p state g) := by
  ext q
  constructor
  · intro hq
    obtain ⟨hh, hr⟩ := Finset.mem_inter.mp hq
    have hrail := (Finset.mem_filter.mp hr).2
    by_cases he : q.1.val = p.x g.left + 1 ∨ q.1.val = p.x g.right - 1
    · apply (finite_mem p _ q).mpr
      apply (wire_near_mem p state g _).mpr
      exact ⟨hrail.1, by
        have hx := readLength_add_lt_x p g.right 0
        rcases he with he | he <;> omega⟩
    · rw [wire_full_split l p hl state hg hw] at hh
      rcases Finset.mem_union.mp hh with hrest | hpair
      · obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hrest
        exact False.elim (wire_rest_clear l p hl hM ha state hg hw
          ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩) hrail.1 (by omega) (by omega))
      · exact wire_pair_rail_near p state g hpair hr
  · intro hq
    refine Finset.mem_inter.mpr ⟨?_, wire_near_subset_rail l p hl state hg hw hq⟩
    rw [wire_full_split l p hl state hg hw]
    apply Finset.mem_union_right
    obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
    refine (SegmentRecipe.mem_holes _ q).mpr ⟨s, ?_, hc⟩
    rcases List.mem_append.mp hs with hs | hs
    · exact List.mem_append_left _ (List.mem_of_mem_drop hs)
    · exact List.mem_append_right _ (List.mem_of_mem_drop hs)

/-- Every canonical assignment gives exactly three holes on each actual open ordinary WIRE. -/
theorem encodedSegments_wireOpenRail_card (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) :
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) ∩ wireOpenRail p g).card = 3 := by
  rw [l.encodedSegments_wireOpenRail p hl hM ha state hg hw, SegmentRecipe.holes_card_of_bounds]
  · exact endpointHorizontals_card p state (wireLeft g) (wireRight g)
      (wire_ports l hl hg hw).1 rfl rfl rfl
  · intro q hq
    obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hq
    have hp := wire_endpoints l hg hw
    have hs' : s ∈ l.signalSegments p state := by
      apply List.mem_append_left
      rcases List.mem_append.mp hs with hs | hs
      · exact List.mem_flatMap.mpr ⟨wireLeft g, hp.1, List.mem_of_mem_drop hs⟩
      · exact List.mem_flatMap.mpr ⟨wireRight g, hp.2, List.mem_of_mem_drop hs⟩
    have hb := l.signalSegments_contains_bounds p hl ha state hs' hc
    omega

/-- The initial physical inventory of an actual ordinary open WIRE. -/
theorem physicalInstance_wireOpenRail_initial_holes (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) :
    (holes (l.physicalInstance p hl hM ha initial target).initial ∩ wireOpenRail p g).card = 3 := by
  rw [l.physicalInstance_initial_holes p hl hM ha initial target]
  exact l.encodedSegments_wireOpenRail_card p hl hM ha initial hg hw

/-- The exact physical goal has the same three holes on that ordinary WIRE. -/
theorem physicalInstance_wireOpenRail_target_holes (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {t : State (p.W + 1) (p.H + 1)}
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    (holes t ∩ wireOpenRail p g).card = 3 := by
  have hh : holes t = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target) := by
    change (t.boxes : Finset (Cell (p.W + 1) (p.H + 1)))ᶜ = _
    rw [ht]
    exact l.physicalInstance_goal_holes p hl hM ha initial target
  rw [hh]
  exact l.encodedSegments_wireOpenRail_card p hl hM ha target hg hw

end PushPuzzle.PushS.PortLayout
