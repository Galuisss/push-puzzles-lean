/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortSignalLocality
import all PushS.PortSignalLocality
import all PushS.PortCoreCrossing
import all PushS.PortEndpointSeparation
import all PushS.PortSegments

/-! Separation of the complete marked fixed-hole background from physical signals. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction SegmentRecipe

private theorem axis_in_streetColumns (l : PortLayout) (p : Scales.Parameters) {i : ℕ}
    (hi : i < l.portCount) : p.x i ∈ streetColumns l (coordinates p) := by
  simp only [streetColumns, List.mem_append, or_assoc]
  right
  left
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

private theorem guard_axis_far (l : PortLayout) (p : Scales.Parameters) (ss : List Segment)
    {x i : ℕ} (hx : x ∈ guardColumns l (coordinates p) ss) (hi : i < l.portCount) :
    14 < Nat.dist x (p.x i) := by
  obtain ⟨s, _, hx⟩ := List.mem_filterMap.mp hx
  split at hx
  · rename_i hcond
    simp only [Option.some.injEq] at hx
    subst x
    have ht := List.all_eq_true.mp hcond.2.2.2 _ (axis_in_streetColumns l p hi)
    exact of_decide_eq_true ht
  · cases hx

private theorem central_no_signal (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {q : ℕ × ℕ} (hlo : p.D - 4 ≤ q.2) (hhi : q.2 ≤ p.D + 4)
    (hq : q ∈ pointHoles (l.signalSegments p state)) : False := by
  have hgap := l.signalSegments_central_gap p state hq
  omega

private theorem interiorFixed_disjoint_signals (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState) :
    Disjoint (pointHoles (interiorFixed l (coordinates p))) (pointHoles (l.signalSegments p state)) := by
  apply Finset.disjoint_left.mpr
  intro q hfixed hsignal
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hfixed
  dsimp only [interiorFixed] at hs
  simp only [List.mem_append, or_assoc] at hs
  rcases hs with hs | hs | hs | hs | hs
  · have hd := l.endpointsFixed_disjoint_signalSegments p hl hM state
    exact Finset.disjoint_left.mp hd ((mem_pointHoles _ q).mpr ⟨s, hs, hq⟩) hsignal
  · obtain ⟨middle, hm, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨kind, first, hg, rfl⟩ := center_gate_mem l hm
    have hd := l.gateFixedSegments_disjoint_signalSegments p hl state hg
    exact Finset.disjoint_left.mp hd ((mem_pointHoles _ q).mpr ⟨s, hs, hq⟩) hsignal
  · exact Finset.disjoint_left.mp (wideFixed_disjoint_signals l p hl state .upper)
      ((mem_pointHoles _ q).mpr ⟨s, hs, hq⟩) hsignal
  · exact Finset.disjoint_left.mp (wideFixed_disjoint_signals l p hl state .lower)
      ((mem_pointHoles _ q).mpr ⟨s, hs, hq⟩) hsignal
  · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
    have hp := point_coordinates hq
    have hy : q.2 = p.D := hp.2
    exact central_no_signal l p state (by omega) (by omega) hsignal

private theorem shifted_disjoint_signals (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (state : SignalState) (ss source : List Segment) (rows : List ℕ)
    (hd : Disjoint (pointHoles ss) (pointHoles (l.signalSegments p state))) :
    Disjoint (pointHoles (ss.map (shiftPoint (guardColumns l (coordinates p) source) rows)))
      (pointHoles (l.signalSegments p state)) := by
  apply Finset.disjoint_left.mpr
  intro q hfixed hsignal
  obtain ⟨image, himage, hq⟩ := (mem_pointHoles _ q).mp hfixed
  obtain ⟨s, hs0, heq⟩ := List.mem_map.mp himage
  subst image
  unfold shiftPoint at hq
  split at hq
  · rename_i hcond
    have hx : s.start.1 ∈ guardColumns l (coordinates p) source := by
      simpa only [List.contains_iff_mem] using hcond.2.1
    obtain ⟨i, hi, hnear⟩ := l.signalSegments_near_axis p hl state hsignal
    have hfar := guard_axis_far l p source hx hi
    have hp := point_coordinates hq
    have hmod := Nat.mod_lt s.start.1 (by decide : 0 < 2)
    rw [hp.1] at hnear
    simp only [Nat.dist_eq_max_sub_min] at hnear hfar
    omega
  · exact Finset.disjoint_left.mp hd ((mem_pointHoles _ q).mpr ⟨s, hs0, hq⟩) hsignal

private theorem markedInterior_disjoint_signals (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState) :
    Disjoint (pointHoles (markedInterior l (coordinates p))) (pointHoles (l.signalSegments p state)) := by
  unfold markedInterior
  extract_lets base guards shifted aux marked
  have hbase : Disjoint (pointHoles base) (pointHoles (l.signalSegments p state)) :=
    interiorFixed_disjoint_signals l p hl hM state
  have hshift : Disjoint (pointHoles shifted) (pointHoles (l.signalSegments p state)) := by
    dsimp only [shifted]
    split
    · exact shifted_disjoint_signals l p hl state _ _ _ hbase
    · exact hbase
  have hmarked : Disjoint (pointHoles marked) (pointHoles (l.signalSegments p state)) := by
    rw [pointHoles_append, Finset.disjoint_union_left]
    refine ⟨hshift, Finset.disjoint_left.mpr ?_⟩
    intro q hfixed hsignal
    obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hfixed
    obtain ⟨x, _, hs⟩ := List.mem_flatMap.mp hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    all_goals have hp := point_coordinates hq
    all_goals simp only [coordinates] at hp
    all_goals exact central_no_signal l p state (by omega) (by omega) hsignal
  change Disjoint (pointHoles ((marked ++ _) ++ _)) _
  rw [pointHoles_append, pointHoles_append, Finset.disjoint_union_left, Finset.disjoint_union_left]
  refine ⟨⟨hmarked, Finset.disjoint_left.mpr ?_⟩, Finset.disjoint_left.mpr ?_⟩
  · intro q hfixed hsignal
    obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hfixed
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
    have hp := point_coordinates hq
    simp only [coordinates] at hp
    exact central_no_signal l p state (by omega) (by omega) hsignal
  · intro q hfixed hsignal
    obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hfixed
    obtain ⟨i, _, hs⟩ := List.mem_flatMap.mp hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    all_goals have hp := point_coordinates hq
    all_goals simp only [coordinates] at hp
    all_goals exact central_no_signal l p state (by omega) (by omega) hsignal

private theorem endpoint_signal_y_interior (p : Scales.Parameters) (state : SignalState)
    (e : Endpoint) (hj : 1 ≤ e.level) (hm : e.level ≤ p.levels) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (endpointSegments (coordinates p) state e)) : 0 < q.2 ∧ q.2 < p.H := by
  have hu : 16384 ≤ (coordinates p).depth e.level := readDepth_ge p hj hm
  have hh : (coordinates p).depth e.level + 64 < p.H := readDepth_add_lt_H p e.level
  have hb := Bool.toNat_le (if e.side = .upper then state.axes.getD e.port false
    else !(state.axes.getD e.port false))
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
  dsimp only [endpointSegments] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · have hv := vertical_coordinates hq
    cases hside : e.side <;> simp [onSide, hside, coordinates] at hu hh hb hv ⊢ <;> omega
  · have hy := horizontal_coordinates hq
    cases hside : e.side <;> simp [onSide, hside, coordinates] at hu hh hy ⊢ <;> omega

private theorem gate_signal_y_interior (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (gateSegments (coordinates p) state kind first internal)) :
    0 < q.2 ∧ q.2 < p.H := by
  have hb := gateSegments_working_band p state kind first internal hq
  have hu := readDepth_ge p (by omega : 1 ≤ 1) p.levels_pos
  have hh := readDepth_add_lt_H p 1
  omega

/-- All actual physical signal holes lie strictly inside the allocated frame. -/
theorem signalSegments_interior (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (l.signalSegments p state)) :
    0 < q.1 ∧ q.1 < p.W ∧ 0 < q.2 ∧ q.2 < p.H := by
  obtain ⟨i, hi, hnear⟩ := l.signalSegments_near_axis p hl state hq
  have hx := readLength_add_lt_x p i 0
  have hright := x_add_readLength_lt_W p (hi.trans_le ha) 0
  have hy : 0 < q.2 ∧ q.2 < p.H := by
    obtain ⟨s, hs, hqs⟩ := (mem_pointHoles _ q).mp hq
    rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
      have hj := l.endpoints_level_bounds p hl hM he
      exact endpoint_signal_y_interior p state e hj.1 hj.2 ((mem_pointHoles _ q).mpr ⟨s, hs, hqs⟩)
    · obtain ⟨g, _, hs⟩ := List.mem_flatMap.mp hs
      cases hgate : g.gate with
      | none => simp [tripleSignal, hgate] at hs
      | some kind =>
        exact gate_signal_y_interior p state kind g.left g.internal
          ((mem_pointHoles _ q).mpr ⟨s, by simpa [tripleSignal, hgate] using hs, hqs⟩)
  simp only [Nat.dist_eq_max_sub_min] at hnear
  omega

private theorem frame_disjoint_signals (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState) :
    Disjoint (pointHoles (frame (coordinates p))) (pointHoles (l.signalSegments p state)) := by
  apply Finset.disjoint_left.mpr
  intro q hframe hsignal
  have hb := l.signalSegments_interior p hl hM ha state hsignal
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hframe
  simp only [frame, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl <;> simp [segment, Segment.Contains, coordinates] at hq <;> omega

/-- The complete actual marked fixed-hole background is disjoint from all physical signals. -/
theorem fixedSegments_disjoint_signalSegments (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) : Disjoint (pointHoles (l.fixedSegments p))
      (pointHoles (l.signalSegments p state)) := by
  unfold fixedSegments
  rw [pointHoles_append, Finset.disjoint_union_left]
  exact ⟨frame_disjoint_signals l p hl hM ha state,
    markedInterior_disjoint_signals l p hl hM state⟩

/-- The finite emitted hole inventory is exactly the sum of the full fixed and signal inventories. -/
theorem encodedSegments_holes_card_eq_add (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) :
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state)).card =
      (pointHoles (l.fixedSegments p)).card + (pointHoles (l.signalSegments p state)).card := by
  rw [l.encodedSegments_holes_card p hl ha state, encodedSegments, pointHoles_append,
    Finset.card_union_of_disjoint (l.fixedSegments_disjoint_signalSegments p hl hM ha state)]

end PushPuzzle.PushS.PortLayout
