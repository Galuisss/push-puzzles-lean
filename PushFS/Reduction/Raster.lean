/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.Refinement
public import PushFS.Reduction.VertexTable
public import PushFS.UnarySum

/-!
# Executable finite support and ownership of the refined source grid

The support rectangle is computed from unary endpoint coordinates and real
source vertices. Searching the actual route table chooses a real source edge.
Away from the actual vertex anchors the separated drawing makes this owner
unique. All support and query operations have machine PT certificates.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Raster


open Cslib.Complexity.NCL Plan Turing.MultiTapeTM ComputableInPolyTime
open scoped PushPuzzle.PushFS.Reduction PushPuzzle.PushFS.Reduction.Plan

/-- Actual endpoints and actual vertex anchors needed to bound every emitted lattice cell. -/
def support (w : Word) : List GridRouting.Point :=
  (refinedProgram w).flatMap (fun r => r.path.flatMap fun s => [s.start, s.finish]) ++
    (vertexRecords w).map (fun v => refinePoint v.point)

/-- Explicit width with a two-cell right-hand exterior margin. -/
def width (w : Word) : ℕ := ((support w).map Prod.fst).sum + 3

/-- Explicit height with a two-cell lower exterior margin. -/
def height (w : Word) : ℕ := ((support w).map Prod.snd).sum + 3

/-- The real refined coarse grid from which the physical atlas is selected. -/
abbrev Cell (w : Word) := PushFS.Cell (width w) (height w)

/-- One route's executable complete point trace. -/
def pointTest (q : Route × GridRouting.Point) : Bool :=
  q.1.path.any (fun s => Segment.containsTest (s, q.2))

private theorem pointTest_correct (r : Route) (p : GridRouting.Point) :
    pointTest (r, p) = true ↔ ∃ s ∈ r.path, s.Contains p := by
  simp [pointTest, Segment.containsTest]

/-- Read the first actual source edge represented at a grid point. -/
def owner (q : Word × GridRouting.Point) : Option ℕ :=
  ((refinedProgram q.1).find? fun r => pointTest (r, q.2)).map Route.edge

@[fun_prop] theorem support_polyTime :
    ComputableInPolyTime support encWord (encList Bitmap.encPoint) := by
  have hr := refinedProgram_polyTime
  have hv := vertexRecords_polyTime
  unfold support
  fun_prop

@[fun_prop] theorem width_polyTime : ComputableInPolyTime width encWord encUnary := by
  unfold width
  fun_prop

@[fun_prop] theorem height_polyTime : ComputableInPolyTime height encWord encUnary := by
  unfold height
  fun_prop

@[fun_prop] theorem pointTest_polyTime :
    ComputableInPolyTime pointTest (encPair encRoute Bitmap.encPoint) encBool := by
  unfold pointTest
  fun_prop

/-- The search charges the complete refined route table and every finite segment lookup. -/
theorem owner_polyTime :
    ComputableInPolyTime owner (encPair encWord Bitmap.encPoint) (encOption encUnary) := by
  have hr : ComputableInPolyTime (fun q : Word × GridRouting.Point => refinedProgram q.1)
      (encPair encWord Bitmap.encPoint) (encList encRoute) :=
    refinedProgram_polyTime.comp (ComputableInPolyTime.fst encWord Bitmap.encPoint)
  have ht : ComputableInPolyTime (fun q : GridRouting.Point × Route => pointTest (q.2, q.1))
      (encPair Bitmap.encPoint encRoute) encBool := by fun_prop
  have hf := ComputableInPolyTime.findWith ht (ComputableInPolyTime.snd encWord Bitmap.encPoint) hr
  unfold owner
  fun_prop

theorem width_pos (w : Word) : 0 < width w := by unfold width; omega
theorem height_pos (w : Word) : 0 < height w := by unfold height; omega

private theorem support_bounds (w : Word) {p : GridRouting.Point} (hp : p ∈ support w) :
    p.1 + 3 ≤ width w ∧ p.2 + 3 ≤ height w := by
  have hx := List.le_sum_of_mem (List.mem_map.mpr ⟨p, hp, rfl⟩ : p.1 ∈ (support w).map Prod.fst)
  have hy := List.le_sum_of_mem (List.mem_map.mpr ⟨p, hp, rfl⟩ : p.2 ∈ (support w).map Prod.snd)
  unfold width height
  omega

/-- Every actual refined edge pixel fits in the computed explicit rectangle with its exterior margin. -/
theorem trace_bounds (w : Word) {e : ℕ} {p : GridRouting.Point}
    (hp : Route.Trace (refinedProgram w) e p) : p.1 + 3 ≤ width w ∧ p.2 + 3 ≤ height w := by
  obtain ⟨r, hr, _, s, hs, hp⟩ := hp
  have hstart : s.start ∈ support w := List.mem_append_left _
    (List.mem_flatMap.mpr ⟨r, hr, List.mem_flatMap.mpr ⟨s, hs, by simp⟩⟩)
  have hfinish : s.finish ∈ support w := List.mem_append_left _
    (List.mem_flatMap.mpr ⟨r, hr, List.mem_flatMap.mpr ⟨s, hs, by simp⟩⟩)
  have hsB := support_bounds w hstart
  have htB := support_bounds w hfinish
  have hpB := s.coordinate_bounds hp
  omega

/-- Every actual source gate anchor also fits in the same explicit support rectangle. -/
theorem vertex_bounds (w : Word) {v : VertexData} (hv : v ∈ vertexRecords w) :
    (refinePoint v.point).1 + 3 ≤ width w ∧ (refinePoint v.point).2 + 3 ≤ height w :=
  support_bounds w (List.mem_append_right _ (List.mem_map.mpr ⟨v, hv, rfl⟩))

/-- Every returned owner is a real edge on that exact emitted pixel. -/
theorem owner_sound {w : Word} {p : GridRouting.Point} {e : ℕ}
    (he : owner (w, p) = some e) : Route.Trace (refinedProgram w) e p := by
  unfold owner at he
  obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp he
  exact ⟨r, List.mem_of_find?_eq_some hr, he, (pointTest_correct r p).mp (List.find?_some (p := fun r => pointTest (r, p)) hr)⟩

/-- Empty ownership means precisely that the point is outside every actual source route. -/
theorem owner_none_iff (w : Word) (p : GridRouting.Point) :
    owner (w, p) = none ↔ ¬∃ e, Route.Trace (refinedProgram w) e p := by
  cases hh : (refinedProgram w).find? (fun r => pointTest (r, p)) with
  | none =>
    constructor
    · intro _
      rintro ⟨e, r, hr, _, hp⟩
      exact (List.find?_eq_none.mp hh r hr) ((pointTest_correct r p).mpr hp)
    · intro _
      simp only [owner, hh, Option.map_none]
  | some r =>
    constructor
    · intro he
      simp only [owner, hh, Option.map_some, reduceCtorEq] at he
    · intro hn
      exact False.elim (hn ⟨r.edge, r, List.mem_of_find?_eq_some hh, rfl,
        (pointTest_correct r p).mp (List.find?_some (p := fun r => pointTest (r, p)) hh)⟩)

/-- At an ordinary wire pixel, the executable owner lookup recovers its unique original source edge. -/
theorem owner_unique {w : Word} (hP : w.checkPlane = true) (hT : w.WellTyped [] [])
    {p : GridRouting.Point} (hvertex : ¬∃ q, VertexPointFrom w ⟨[], 0, []⟩ 0 q ∧ p = refinePoint q)
    {e : ℕ} (he : Route.Trace (refinedProgram w) e p) : owner (w, p) = some e := by
  cases hh : owner (w, p) with
  | none => exact False.elim ((owner_none_iff w p).mp hh ⟨e, he⟩)
  | some f =>
    have hf := owner_sound hh
    by_cases hfe : f = e
    · simp only [hfe]
    · exact False.elim (hvertex (refinedProgram_separated hP hT hfe hf he))

end PushPuzzle.PushFS.Reduction.Raster
