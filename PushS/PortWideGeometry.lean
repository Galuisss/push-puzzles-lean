/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortTwoPageStreets
public import PushS.PortCentralMargins
import all PushS.PortSegments
import all PushS.PortSignalLocality
import all PushS.PortCoreCrossing
import all PushS.PortCentralMargins
import all PushS.PortTwoPageStreets
import all PushS.PortEndpointSeparation
import all PushS.PortStreetSeparation

/-!
# Wide separator columns exceed the complete physical hole budget

Every original street lies within the last branch length of a grid axis or side frame.
An adjacent page-column gap wider than that length spans two grid axes. Its midpoint
therefore stays beyond the global hole budget from every original street column.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction SegmentRecipe

/-- The actual emitted wide separator points on one page before conditional even rounding. -/
def wideSeparatorSegments (l : PortLayout) (p : Scales.Parameters) (side : Side) : List Segment :=
  wideFixed l (coordinates p) side

private def physicalWideSegments (l : PortLayout) (p : Scales.Parameters) (side : Side) :
    List Segment :=
  let c := coordinates p
  let guards := guardColumns l c (frame c ++ interiorFixed l c)
  if guards.any (fun x => guards.contains (x + 1)) then
    (wideFixed l c side).map (shiftPoint guards (streetRows c)) else wideFixed l c side

/-- Actual finite wide separator holes after the complete emitter's conditional even rounding. -/
def wideSeparatorHoles (l : PortLayout) (p : Scales.Parameters) :
    Finset (PushFS.Cell (p.W + 1) (p.H + 1)) :=
  SegmentRecipe.holes (p.W + 1) (p.H + 1)
    (physicalWideSegments l p .upper ++ physicalWideSegments l p .lower)

private def NearGrid (l : PortLayout) (p : Scales.Parameters) (side : Side) (x : ℕ) : Prop :=
  ∃ k, k * p.D ∈ pageColumns l (coordinates p) side ∧
    x ≤ k * p.D + p.L p.levels ∧ k * p.D ≤ x + p.L p.levels

private theorem axis_near_grid (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) {i x : ℕ} (hi : i < l.portCount)
    (hx : x ≤ p.x i + p.L p.levels) (hx' : p.x i ≤ x + p.L p.levels) :
    NearGrid l p side x :=
  ⟨i + 1, axis_in_pageColumns l p hl side hi, hx, hx'⟩

private theorem streetColumn_near_grid (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) {x : ℕ} (hx : x ∈ streetColumns l (coordinates p)) : NearGrid l p side x := by
  have hL := length_floor p
  simp only [streetColumns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hx
  change x = 0 ∨ x = p.W ∨ _ at hx
  rcases hx with rfl | rfl | hx | hx
  · refine ⟨0, ?_, by simp, by simp⟩
    simp [pageColumns]
  · refine ⟨p.axes + 1, ?_, by change p.W ≤ p.W + _; omega, by change p.W ≤ p.W + _; omega⟩
    change p.W ∈ pageColumns l (coordinates p) side
    simp [pageColumns, coordinates]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact axis_near_grid l p hl side (List.mem_range.mp hi)
      (by change p.x i ≤ p.x i + _; omega) (by change p.x i ≤ p.x i + _; omega)
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
      have hi := l.endpoints_port_lt hl he
      have hn := auxiliary_near_axis p e
      rcases List.mem_cons.mp hx with rfl | hx
      · exact axis_near_grid l p hl side hi hn.2.1 hn.1
      · have heq : x = (auxiliary (coordinates p) e).2 := List.mem_singleton.mp hx
        subst x
        exact axis_near_grid l p hl side hi hn.2.2.2 hn.2.2.1
    · obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨kind, first, hg, he⟩ := center_gate_mem l hi
      have hi' : i < l.portCount := by rw [he]; exact gate_middle_lt l hl hg
      have hm := readLength_add_lt_x p i 0
      simp only [specialColumns, List.mem_cons, List.not_mem_nil, or_false] at hx
      change x = p.x i - 2 ∨ x = p.x i + 4 ∨ x = p.x i + 6 ∨ x = p.x i + 8 ∨ x = p.x i + 12 at hx
      exact axis_near_grid l p hl side hi' (by omega) (by omega)

private theorem grid_separated (D a b : ℕ) :
    a * D = b * D ∨ a * D + D ≤ b * D ∨ b * D + D ≤ a * D := by
  rcases lt_trichotomy a b with h | rfl | h
  · right; left
    simpa only [Nat.add_mul, Nat.one_mul] using
      Nat.mul_le_mul_right D (show a + 1 ≤ b by omega)
  · exact Or.inl rfl
  · right; right
    simpa only [Nat.add_mul, Nat.one_mul] using
      Nat.mul_le_mul_right D (show b + 1 ≤ a by omega)

private theorem wide_gap_grid_spacing (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) {a b : ℕ} (hab : (a, b) ∈ adjacentPairs (pageColumns l (coordinates p) side))
    (hwide : p.L p.levels < b - a) : p.D ≤ b - a + 2 * p.L p.levels := by
  obtain ⟨ha, hb⟩ := adjacentPair_mem hab
  have hab' := (adjacentPair_gap hab).1
  obtain ⟨i, hi, hai, hia⟩ := streetColumn_near_grid l p hl side
    (pageColumn_mem_street l p hl side ha)
  obtain ⟨j, _, hbj, hjb⟩ := streetColumn_near_grid l p hl side
    (pageColumn_mem_street l p hl side hb)
  have hno := (adjacentPair_gap hab).2 _ hi
  have hD := p.outer_distance
  rcases grid_separated p.D i j with hij | hij | hij <;> omega

private theorem midpoint_street_distance (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) {a b x : ℕ}
    (hab : (a, b) ∈ adjacentPairs (pageColumns l (coordinates p) side))
    (hwide : p.L p.levels < b - a) (hx : x ∈ streetColumns l (coordinates p)) :
    2 * p.b p.levels + 4 < Nat.dist ((a + b) / 2) x := by
  have hg := wide_gap_grid_spacing l p hl side hab hwide
  have hab' := (adjacentPair_gap hab).1
  obtain ⟨i, hi, hxi, hix⟩ := streetColumn_near_grid l p hl side hx
  have hno := (adjacentPair_gap hab).2 _ hi
  have hD := p.outer_distance
  simp only [Nat.dist]
  omega

/-- Every actual unrounded wide separator point is farther than the complete physical hole
budget from every original street column, with room for its one-cell even rounding. -/
theorem wideSeparatorSegments_street_gap (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (side : Side) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (l.wideSeparatorSegments p side)) :
    ∀ x ∈ l.streetColumnCoordinates p, 2 * p.b p.levels + 4 < Nat.dist q.1 x := by
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
  obtain ⟨⟨a, b⟩, hab, hs⟩ := List.mem_flatMap.mp hs
  dsimp only at hs
  split at hs
  · rename_i hwide
    obtain ⟨y, _, hs⟩ := List.mem_filterMap.mp hs
    split at hs
    · cases hs
    · simp only [Option.some.injEq] at hs
      subst s
      have he := (point_coordinates hq).1
      intro x hx
      rw [he]
      apply midpoint_street_distance l p hl side hab _ hx
      change readLength p p.levels < b - a at hwide
      rwa [readLength_eq p p.levels_pos le_rfl] at hwide
  · cases hs

private theorem wideFixed_mem_interior (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {s : Segment} (hs : s ∈ wideFixed l (coordinates p) side) :
    s ∈ interiorFixed l (coordinates p) := by
  simp only [interiorFixed, List.mem_append, or_assoc]
  cases side
  · exact Or.inr (Or.inr (Or.inl hs))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hs)))

private theorem physicalWide_mem_marked (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {s : Segment} (hs : s ∈ physicalWideSegments l p side) :
    s ∈ markedInterior l (coordinates p) := by
  dsimp only [markedInterior]
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  dsimp only [physicalWideSegments] at hs
  split at hs
  · rename_i hround
    rw [ite_eq_left hround]
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
    exact List.mem_map.mpr ⟨u, wideFixed_mem_interior l p side hu, rfl⟩
  · rename_i hround
    rw [ite_eq_right hround]
    exact wideFixed_mem_interior l p side hs

/-- The selected physical wide separators are actual fixed holes of the complete emitter. -/
theorem wideSeparatorHoles_subset_fixed (l : PortLayout) (p : Scales.Parameters) :
    l.wideSeparatorHoles p ⊆ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.fixedSegments p) := by
  intro q hq
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  have hs' : s ∈ markedInterior l (coordinates p) :=
    (List.mem_append.mp hs).elim (physicalWide_mem_marked l p .upper) (physicalWide_mem_marked l p .lower)
  exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_right _ hs', hq⟩

private theorem wideFixed_is_point (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {s : Segment} (hs : s ∈ wideFixed l (coordinates p) side) : s.start = s.finish := by
  obtain ⟨ab, _, hs⟩ := List.mem_flatMap.mp hs
  dsimp only at hs
  split at hs
  · obtain ⟨y, _, hs⟩ := List.mem_filterMap.mp hs
    split at hs
    · cases hs
    · simp only [Option.some.injEq] at hs
      subst s
      rfl
  · cases hs

private theorem point_start_contains (s : Segment) (hs : s.start = s.finish) : s.Contains s.start := by
  left
  exact ⟨congrArg Prod.fst hs, rfl, min_le_left _ _, le_max_left _ _⟩

private theorem shiftPoint_gap (l : PortLayout) (p : Scales.Parameters) (guards rows : List ℕ)
    {s : Segment} (hs : s.start = s.finish)
    (hgap : ∀ x ∈ l.streetColumnCoordinates p, 2 * p.b p.levels + 4 < Nat.dist s.start.1 x)
    {q : ℕ × ℕ} (hq : (shiftPoint guards rows s).Contains q) :
    ∀ x ∈ l.streetColumnCoordinates p, 2 * p.b p.levels + 2 < Nat.dist q.1 x := by
  intro x hx
  have hg := hgap x hx
  unfold shiftPoint at hq
  split at hq
  · have he := (point_coordinates hq).1
    simp only [Nat.dist] at *
    omega
  · simp only [Segment.Contains, ← hs] at hq
    simp only [Nat.dist] at *
    omega

private theorem physicalWide_gap (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) {s : Segment} (hs : s ∈ physicalWideSegments l p side) {q : ℕ × ℕ}
    (hq : s.Contains q) :
    ∀ x ∈ l.streetColumnCoordinates p, 2 * p.b p.levels + 2 < Nat.dist q.1 x := by
  dsimp only [physicalWideSegments] at hs
  split at hs
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
    have hp := wideFixed_is_point l p side hu
    have hm := (mem_pointHoles _ u.start).mpr ⟨u, hu, point_start_contains u hp⟩
    exact shiftPoint_gap l p _ _ hp (l.wideSeparatorSegments_street_gap p hl side hm) hq
  · have hp := wideFixed_is_point l p side hs
    have hm := (mem_pointHoles _ s.start).mpr ⟨s, hs, point_start_contains s hp⟩
    intro x hx
    have hg := l.wideSeparatorSegments_street_gap p hl side hm x hx
    simp only [Segment.Contains, ← hp] at hq
    simp only [Nat.dist] at *
    omega

/-- Every actual wide separator, including its conditional rounding, is beyond the full
physical hole budget from all original street columns. -/
theorem wideSeparatorHoles_street_gap (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {q : PushFS.Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.wideSeparatorHoles p) :
    ∀ x ∈ l.streetColumnSet p, 2 * p.b p.levels + 2 < Nat.dist q.1.val x.val := by
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  intro x hx
  exact (List.mem_append.mp hs).elim
    (fun hs => physicalWide_gap l p hl .upper hs hq x.val hx)
    (fun hs => physicalWide_gap l p hl .lower hs hq x.val hx)

private theorem wideFixed_working_row (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {s : Segment} (hs : s ∈ wideFixed l (coordinates p) side) :
    ∃ y ∈ workingDepthCoordinates l p, s.start.2 = if side = .upper then y else p.H - y := by
  obtain ⟨ab, _, hs⟩ := List.mem_flatMap.mp hs
  dsimp only at hs
  split at hs
  · obtain ⟨y, hy, hs⟩ := List.mem_filterMap.mp hs
    split at hs
    · cases hs
    · simp only [Option.some.injEq] at hs
      subst s
      exact ⟨y, hy, by simp only [point, segment, Nat.min_self, onSide, coordinates]⟩
  · cases hs

private theorem physicalWide_point_row (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {s : Segment} (hs : s ∈ physicalWideSegments l p side) :
    s.start = s.finish ∧ ∃ y ∈ workingDepthCoordinates l p,
      s.start.2 = if side = .upper then y else p.H - y := by
  dsimp only [physicalWideSegments] at hs
  split at hs
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
    have hp := wideFixed_is_point l p side hu
    have hr := wideFixed_working_row l p side hu
    unfold shiftPoint
    split
    · exact ⟨rfl, by simpa only [point, segment, Nat.min_self] using hr⟩
    · exact ⟨hp, hr⟩
  · exact ⟨wideFixed_is_point l p side hs, wideFixed_working_row l p side hs⟩

/-- Every physical wide separator lies on a reflected actual working depth. -/
theorem wideSeparatorHoles_depth (l : PortLayout) (p : Scales.Parameters)
    {q : PushFS.Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.wideSeparatorHoles p) :
    ∃ side : Side, ∃ y ∈ l.workingDepthCoordinates p,
      q.2.val = if side = .upper then y else p.H - y := by
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  have hrow (side : Side) (hs : s ∈ physicalWideSegments l p side) :
      ∃ y ∈ l.workingDepthCoordinates p, q.2.val = if side = .upper then y else p.H - y := by
    obtain ⟨hp, y, hy, he⟩ := physicalWide_point_row l p side hs
    simp only [Segment.Contains, ← hp] at hq
    have hqy : q.2.val = s.start.2 := by omega
    exact ⟨y, hy, hqy.trans he⟩
  rcases List.mem_append.mp hs with hs | hs
  · exact ⟨.upper, hrow .upper hs⟩
  · exact ⟨.lower, hrow .lower hs⟩

/-- Every physical wide separator remains on its actual selected working row after rounding. -/
theorem wideSeparatorHoles_working_row (l : PortLayout) (p : Scales.Parameters)
    {q : PushFS.Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.wideSeparatorHoles p) :
    q.2 ∈ l.workingRowSet p := by
  obtain ⟨side, y, hy, he⟩ := l.wideSeparatorHoles_depth p hq
  exact l.mem_workingRowSet_of_onSide p hy side q.2 he

private theorem workingDepth_positive (l : PortLayout) (p : Scales.Parameters) {y : ℕ}
    (hy : y ∈ l.workingDepthCoordinates p) : 0 < y ∧ y < p.H := by
  obtain ⟨j, hj, hy⟩ := List.mem_flatMap.mp hy
  have hj' := List.mem_range.mp hj
  change j < p.levels at hj'
  have hb := readDepth_ge p (j := j + 1) (by omega) (by omega)
  have hu := readDepth_add_lt_H p (j + 1)
  change 16384 ≤ (coordinates p).depth (j + 1) at hb
  change (coordinates p).depth (j + 1) + 64 < p.H at hu
  dsimp only at hy
  split at hy <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hy <;> omega

/-- Actual wide separators are interior cells of the physical rectangle. -/
theorem wideSeparatorHoles_off_frame (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {q : PushFS.Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.wideSeparatorHoles p) :
    q ∉ Boundary.frame := by
  have hgap := l.wideSeparatorHoles_street_gap p hl hq
  have hlft := hgap (⟨0, by omega⟩ : Fin (p.W + 1)) (by
    change 0 ∈ streetColumns l (coordinates p); simp [streetColumns])
  have hrgt := hgap (⟨p.W, by omega⟩ : Fin (p.W + 1)) (by
    change p.W ∈ streetColumns l (coordinates p); simp [streetColumns, coordinates])
  obtain ⟨side, y, hy, he⟩ := l.wideSeparatorHoles_depth p hq
  have hdepth := workingDepth_positive l p hy
  have hrow : 0 < q.2.val ∧ q.2.val < p.H := by
    cases side <;> simp only [ite_true, reduceCtorEq, ite_false] at he <;> omega
  intro hf
  obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
  simp only [Nat.dist] at hlft hrgt
  cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd <;> omega

end PushPuzzle.PushS.PortLayout
