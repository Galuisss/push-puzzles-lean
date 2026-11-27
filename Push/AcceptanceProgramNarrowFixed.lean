/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramNonpoint
import all Push.AcceptanceProgramLayout
import all PushS.PortSegments
import all PushS.PortPointBudget
import all PushS.PortWalkBudget
import all PushS.PortStreetSeparation

/-! Actual fixed marker rows retained by the second acceptance clear. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- Exact rows retained at the second row clear, including the gate's private bridge. -/
def secondRowKeep (l : PortLayout) (p : Scales.Parameters) : Finset ℕ :=
  keepRows l p ∪ {p.H - p.Y 1 - 1}

/-- Selected working rows survive the second clear. -/
theorem working_row_narrow (l : PortLayout) (p : Scales.Parameters) (side : Side) {depth : ℕ}
    (hd : depth ∈ l.workingDepthCoordinates p) :
    (if side = .upper then depth else p.H - depth) ∈ secondRowKeep l p := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply List.mem_toFinset.mpr
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨depth, hd, ?_⟩
  cases side <;> simp

private theorem cut_row_keep_narrow (l : PortLayout) (p : Scales.Parameters) {row : ℕ}
    (hrow : row ∈ cutRows p) :
    row ∈ secondRowKeep l p := by
  simp only [secondRowKeep, keepRows, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr hrow))

theorem marker_row_keep_narrow (l : PortLayout) (p : Scales.Parameters) {row : ℕ}
    (hrow : row ∈ ({p.D - 2, p.D + 2, p.D - 4, p.D + 4} : Finset ℕ)) : row ∈ secondRowKeep l p := by
  simp only [secondRowKeep, keepRows, Finset.mem_union]
  exact Or.inl (Or.inr hrow)

private theorem interlevel_row_keep_narrow (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {j : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) :
    (if side = .upper then (p.Y j + p.Y (j + 1)) / 2
      else p.H - (p.Y j + p.Y (j + 1)) / 2) ∈ secondRowKeep l p := by
  apply cut_row_keep_narrow l p
  apply List.mem_toFinset.mpr
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨j - 1, List.mem_range.mpr (by omega), ?_⟩
  have he : j - 1 + 1 = j := by omega
  have he' : j - 1 + 2 = j + 1 := by omega
  simp only [he, he']
  cases side <;> simp

private theorem half_row_keep_narrow (l : PortLayout) (p : Scales.Parameters) :
    p.H - p.Y 1 / 2 ∈ secondRowKeep l p := by
  apply cut_row_keep_narrow l p
  simp only [cutRows, List.mem_toFinset, List.mem_append, List.mem_cons]
  tauto

private theorem central_row_keep_narrow (l : PortLayout)
    (p : Scales.Parameters) : p.D ∈ secondRowKeep l p := by
  apply cut_row_keep_narrow l p
  simp only [cutRows, List.mem_toFinset, List.mem_append, List.mem_cons]
  tauto

end PushPuzzle.Push.AcceptanceProgram

namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction SegmentRecipe Push.AcceptanceProgram

private theorem endpoint_point_row_narrow (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint) (he : e ∈ l.endpoints)
    {s : Segment} (hs : s ∈ endpointFixedSegments l (coordinates p) e) (hn : s.start = s.finish) :
    s.start.2 ∈ secondRowKeep l p := by
  rw [← List.take_append_drop 3 (endpointFixedSegments l (coordinates p) e), List.mem_append] at hs
  rcases hs with hs | hs
  · exact False.elim (endpoint_base_nonpoint l p hl hM he hs hn)
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
  dsimp only [endpointFixedSegments] at hs
  simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero, List.mem_append] at hs
  rcases hs with hs | hs
  · obtain ⟨v, hv, hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_append.mp hs with hs | hs
    all_goals
      split at hs
      next hsel =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        simp only [point, segment, min_self]
        exact working_row_narrow l p e.side (by simpa only [workingDepthCoordinates] using hv)
      next hsel => cases hs
  · split at hs
    next hlevel =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      have hlevel' : e.level < p.levels := hlevel
      have hread : (depthTable p).getD e.level 0 = p.Y e.level := readDepth_eq p hj hjm
      have hnext : (depthTable p).getD (e.level + 1) 0 = p.Y (e.level + 1) :=
        readDepth_eq p (by omega) (by omega)
      rcases hs with rfl | rfl
      all_goals
        simp only [point, segment, min_self]
        have hh := interlevel_row_keep_narrow l p e.side hj hlevel'
        simpa only [onSide, coordinates, Coordinates.depth, hread, hnext] using hh
    next hlevel => cases hs

private theorem gate_point_row_narrow (l : PortLayout) (p : Scales.Parameters) (middle : ℕ)
    {s : Segment} (hs : s ∈ gateFixedSegments (coordinates p) middle) (hn : s.start = s.finish) :
    s.start.2 ∈ secondRowKeep l p := by
  rw [← List.take_append_drop 4 (gateFixedSegments (coordinates p) middle), List.mem_append] at hs
  rcases hs with hs | hs
  · exact False.elim (gate_base_nonpoint p middle hs hn)
  have hread : (depthTable p).getD 1 0 = p.Y 1 := readDepth_eq p le_rfl p.levels_pos
  dsimp only [gateFixedSegments] at hs
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.drop_succ_cons, List.drop_zero, List.mem_cons] at hs
  rcases hs with rfl | hbranch | rfl | rfl | hmarkers
  · simp only [point, segment, min_self]
    apply Finset.mem_union_right
    simp only [Finset.mem_singleton, onSide, reduceCtorEq, ite_false, coordinates, Coordinates.depth, hread]
    omega
  · subst s
    have hx := congrArg Prod.fst hn
    simp only [segment] at hx
    omega
  · simpa only [point, segment, min_self, onSide, reduceCtorEq, ite_false, coordinates,
      Coordinates.depth, hread] using half_row_keep_narrow l p
  · simpa only [point, segment, min_self, onSide, reduceCtorEq, ite_false, coordinates,
      Coordinates.depth, hread] using half_row_keep_narrow l p
  · split at hmarkers
    next hlevel =>
      obtain ⟨col, _, rfl⟩ := List.mem_map.mp hmarkers
      simp only [point, segment, min_self]
      have hlevel' : 1 < p.levels := hlevel
      have hnext : (depthTable p).getD 2 0 = p.Y 2 := readDepth_eq p (by omega) (by omega)
      have hh := interlevel_row_keep_narrow l p .lower le_rfl hlevel'
      simpa only [onSide, reduceCtorEq, ite_false, coordinates, Coordinates.depth, hread, hnext] using hh
    next hlevel => cases hmarkers

private theorem wide_point_row_narrow (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {s : Segment} (hs : s ∈ wideFixed l (coordinates p) side) : s.start.2 ∈ secondRowKeep l p := by
  obtain ⟨ab, hab, hs⟩ := List.mem_flatMap.mp hs
  dsimp only at hs
  split at hs
  next hsep =>
    obtain ⟨v, hv, hs⟩ := List.mem_filterMap.mp hs
    split at hs
    next hcross => cases hs
    next hcross =>
      cases hs
      simp only [point, segment, min_self]
      exact working_row_narrow l p side (by simpa only [workingDepthCoordinates] using hv)
  next hsep => cases hs

private theorem base_point_row_narrow (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {s : Segment}
    (hs : s ∈ interiorFixed l (coordinates p)) (hn : s.start = s.finish) : s.start.2 ∈ secondRowKeep l p := by
  simp only [interiorFixed, List.mem_append, List.mem_flatMap, List.mem_map, or_assoc] at hs
  rcases hs with ⟨e, he, hs⟩ | ⟨middle, hi, hs⟩ | hu | hd | ⟨x, hx, he⟩
  · exact endpoint_point_row_narrow l p hl hM e he hs hn
  · exact gate_point_row_narrow l p middle hs hn
  · exact wide_point_row_narrow l p .upper hu
  · exact wide_point_row_narrow l p .lower hd
  · subst s
    simpa only [point, segment, min_self, coordinates] using central_row_keep_narrow l p

/-- The complete actual fixed-point target stock lies on rows retained by the first row clear. -/
theorem acceptanceFixedPointNarrowRow (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {s : Segment}
    (hs : s ∈ l.fixedSegments p) (hn : s.start = s.finish)
    {q : Cell (p.W + 1) (p.H + 1)} (hc : s.Contains (q.1.val, q.2.val))
    (hframe : q ∉ Boundary.frame) : q.2.val ∈ secondRowKeep l p := by
  rcases List.mem_append.mp hs with hs | hs
  · exact False.elim (hframe (frame_contains (coordinates p) q ⟨s, hs, hc⟩))
  have hrow : s.start.2 ∈ secondRowKeep l p := by
    unfold markedInterior at hs
    extract_lets base guards shifted aux marked at hs
    change s ∈ ((shifted ++ _) ++ _) ++ _ at hs
    simp only [List.mem_append, or_assoc] at hs
    rcases hs with hs | hs | hs | hs
    · dsimp only [shifted] at hs
      split at hs
      next hadj =>
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
        unfold shiftPoint at hn ⊢
        split_ifs at hn ⊢
        next hshift =>
          simp only [point, segment, min_self]
          exact base_point_row_narrow l p hl hM ht hshift.1
        next hshift => exact base_point_row_narrow l p hl hM ht hn
      next hadj => exact base_point_row_narrow l p hl hM hs hn
    · obtain ⟨x, hx, hs⟩ := List.mem_flatMap.mp hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      all_goals
        apply marker_row_keep_narrow l p
        simp only [point, segment, min_self, coordinates, Finset.mem_insert, Finset.mem_singleton]
        tauto
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
      apply marker_row_keep_narrow l p
      simp only [point, segment, min_self, coordinates, Finset.mem_insert, Finset.mem_singleton]
      tauto
    · obtain ⟨middle, hi, hs⟩ := List.mem_flatMap.mp hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      all_goals
        apply marker_row_keep_narrow l p
        simp only [point, segment, min_self, coordinates, Finset.mem_insert, Finset.mem_singleton]
        tauto
  have hy : q.2.val = s.start.2 := by
    simp only [Segment.Contains, hn] at hc
    have hh := congrArg Prod.snd hn
    omega
  exact hy.symm ▸ hrow

end PushPuzzle.PushS.PortLayout
