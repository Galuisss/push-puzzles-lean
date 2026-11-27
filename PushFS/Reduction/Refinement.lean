/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.VertexIncidence
public import PushFS.Reduction.GeometryChecks

/-!
# Uniform refinement of the actual source paths

Scale integer coordinates by sixteen and add a two-unit margin. All actual
segments remain axis-aligned. Coarse vertices are six rows apart; a refined
intersection between different source edges therefore occurs exactly at the
refinement of a real coarse source vertex, including between coarse anchors.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL Turing.MultiTapeTM ComputableInPolyTime
open scoped PushPuzzle.PushFS.Reduction

/-- A degenerate point, a horizontal segment or a vertical segment. -/
def Segment.AxisAligned (s : Segment) : Prop := s.start.1 = s.finish.1 ∨ s.start.2 = s.finish.2

/-- An aligned segment contains every point of its coordinate intervals. -/
theorem Segment.contains_of_bounds {s : Segment} (ha : s.AxisAligned) {p : ℕ × ℕ}
    (hp : min s.start.1 s.finish.1 ≤ p.1 ∧ p.1 ≤ max s.start.1 s.finish.1 ∧
      min s.start.2 s.finish.2 ≤ p.2 ∧ p.2 ≤ max s.start.2 s.finish.2) : s.Contains p := by
  rcases ha with ha | ha
  · exact Or.inl ⟨ha, by omega, hp.2.2⟩
  · exact Or.inr ⟨ha, by omega, hp.1, hp.2.1⟩

/-- Every serialized instruction of an actual orthogonal path is aligned. -/
private theorem segments_aligned {p q : GridRouting.Point} (r : GridRouting.Path p q) :
    ∀ s ∈ segments r, s.AxisAligned := by
  induction r with
  | horizontal => intro s hs; cases List.mem_singleton.mp hs; exact Or.inr rfl
  | vertical => intro s hs; cases List.mem_singleton.mp hs; exact Or.inl rfl
  | comp r t ihr iht =>
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact ihr s hs
    · exact iht s hs

private theorem Connects.aligned {ss : List Segment} {p q : GridRouting.Point}
    (hs : Connects ss p q) :
    ∀ s ∈ ss, s.AxisAligned := by
  obtain ⟨r, rfl⟩ := hs
  exact segments_aligned r

private theorem Segment.translate_aligned {s : Segment} (hs : s.AxisAligned) (dx dy : ℕ) :
    (s.translate dx dy).AxisAligned := by
  rcases hs with hs | hs <;> simp_all [Segment.AxisAligned, Segment.translate]

/-- Place each old integer point on the refined lattice, with a fixed exterior margin. -/
def refinePoint (p : ℕ × ℕ) : ℕ × ℕ := (16 * p.1 + 32, 16 * p.2 + 32)

/-- Refine the complete closed segment, including the intervening new integer cells. -/
def Segment.refined (s : Segment) : Segment := ⟨refinePoint s.start, refinePoint s.finish⟩

/-- Retain the source edge number on every refined instruction. -/
def Route.refined (r : Route) : Route := ⟨r.edge, r.path.map Segment.refined⟩

private theorem affine_min (a b : ℕ) : min (16 * a + 32) (16 * b + 32) = 16 * min a b + 32 := by omega
private theorem affine_max (a b : ℕ) : max (16 * a + 32) (16 * b + 32) = 16 * max a b + 32 := by omega

/-- Membership at an old lattice anchor has its exact original meaning after refinement. -/
theorem Segment.refined_anchor (s : Segment) (p : ℕ × ℕ) :
    s.refined.Contains (refinePoint p) ↔ s.Contains p := by
  simp only [Segment.refined, refinePoint, Segment.Contains, affine_min, affine_max]
  omega

set_option maxHeartbeats 2000000 in
/-- Refinement creates no fractional intersection if different common coarse pixels cannot be adjacent. -/
private theorem Segment.refined_intersection {s t : Segment} (hs : s.AxisAligned)
    (ht : t.AxisAligned)
    (hcommon : ∀ q r, s.Contains q → t.Contains q → s.Contains r → t.Contains r →
      Nearby 1 q r → q = r) {p : ℕ × ℕ}
    (hp : s.refined.Contains p) (hp' : t.refined.Contains p) :
    ∃ q, s.Contains q ∧ t.Contains q ∧ p = refinePoint q := by
  let xlo := max (min s.start.1 s.finish.1) (min t.start.1 t.finish.1)
  let xhi := min (max s.start.1 s.finish.1) (max t.start.1 t.finish.1)
  let ylo := max (min s.start.2 s.finish.2) (min t.start.2 t.finish.2)
  let yhi := min (max s.start.2 s.finish.2) (max t.start.2 t.finish.2)
  have hpS := s.refined.coordinate_bounds hp
  have hpT := t.refined.coordinate_bounds hp'
  simp only [Segment.refined, refinePoint, affine_min, affine_max] at hpS hpT
  have hb : xlo ≤ xhi ∧ ylo ≤ yhi := by dsimp [xlo, xhi, ylo, yhi]; omega
  have common (x y : ℕ) (hx : xlo ≤ x ∧ x ≤ xhi) (hy : ylo ≤ y ∧ y ≤ yhi) :
      s.Contains (x, y) ∧ t.Contains (x, y) := by
    dsimp [xlo, xhi] at hx
    dsimp [ylo, yhi] at hy
    exact ⟨Segment.contains_of_bounds hs (by dsimp only; omega),
      Segment.contains_of_bounds ht (by dsimp only; omega)⟩
  have hq := common xlo ylo ⟨le_rfl, hb.1⟩ ⟨le_rfl, hb.2⟩
  have hx : xlo = xhi := by
    by_contra hh
    have hr := common (xlo + 1) ylo (by omega) ⟨le_rfl, hb.2⟩
    have he := hcommon _ _ hq.1 hq.2 hr.1 hr.2 (by unfold Nearby; dsimp only; omega)
    have he' := congrArg Prod.fst he
    dsimp only at he'
    omega
  have hy : ylo = yhi := by
    by_contra hh
    have hr := common xlo (ylo + 1) ⟨le_rfl, hb.1⟩ (by omega)
    have he := hcommon _ _ hq.1 hq.2 hr.1 hr.2 (by unfold Nearby; dsimp only; omega)
    have he' := congrArg Prod.snd he
    dsimp only at he'
    omega
  refine ⟨(xlo, ylo), hq.1, hq.2, ?_⟩
  dsimp [xlo, xhi] at hx
  dsimp [ylo, yhi] at hy
  apply Prod.ext <;> dsimp [refinePoint, xlo, ylo] <;> omega

@[fun_prop] theorem refinePoint_polyTime :
    ComputableInPolyTime refinePoint Bitmap.encPoint Bitmap.encPoint := by
  unfold refinePoint Bitmap.encPoint
  fun_prop

@[fun_prop] theorem Segment.refined_polyTime : ComputableInPolyTime Segment.refined encSegment encSegment := by
  unfold Segment.refined
  fun_prop

@[fun_prop] theorem Route.refined_polyTime : ComputableInPolyTime Route.refined encRoute encRoute := by
  unfold Route.refined
  fun_prop

namespace Plan

/-- Every metadata vertex is at least three rows below its suffix boundary. -/
theorem VertexPointFrom.row_lower {w : Word} {st : Word.State} {y : ℕ} {p : GridRouting.Point}
    (hp : VertexPointFrom w st y p) : y + 3 ≤ p.2 := by
  induction hp with
  | here sl w st y =>
    change y + 3 ≤ 2 * (st.wires.length + 1) + 1 + y
    omega
  | later _ ih => omega

/-- Different actual source vertices have at least six rows of separation. -/
private theorem VertexPointFrom.rows_apart {w : Word} {st : Word.State} {y : ℕ}
    {p q : GridRouting.Point}
    (hp : VertexPointFrom w st y p) (hq : VertexPointFrom w st y q) (hne : p ≠ q) :
    p.2 + 6 ≤ q.2 ∨ q.2 + 6 ≤ p.2 := by
  induction w generalizing st y with
  | nil => cases hp
  | cons sl w ih =>
    let l : Layer := ⟨sl, st⟩
    have hmargin : l.vertexPoint.2 + 3 ≤ l.height := by
      unfold Layer.vertexPoint Layer.height Layer.middleY
      omega
    cases hp with
    | here =>
      cases hq with
      | here => exact False.elim (hne rfl)
      | later hq =>
        have hh : y + l.height + 3 ≤ q.2 := hq.row_lower
        left
        change l.vertexPoint.2 + y + 6 ≤ q.2
        omega
    | later hp =>
      cases hq with
      | here =>
        have hh : y + l.height + 3 ≤ p.2 := hp.row_lower
        right
        change l.vertexPoint.2 + y + 6 ≤ p.2
        omega
      | later hq => exact ih hp hq

theorem VertexPointFrom.eq_of_nearby {w : Word} {st : Word.State} {y : ℕ} {p q : GridRouting.Point}
    (hp : VertexPointFrom w st y p) (hq : VertexPointFrom w st y q) (hnear : Nearby 1 p q) : p = q := by
  by_contra he
  have hh := hp.rows_apart hq he
  unfold Nearby at hnear
  omega

/-- Every actual route instruction of a drawn layer is aligned. -/
private theorem Layer.connections_aligned {l : Layer} (h : l.HasDrawing) {r : Route}
    (hr : r ∈ l.connections) :
    ∀ s ∈ r.path, s.AxisAligned := by
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact (l.incoming_connects h ⟨i, List.mem_range.mp hi⟩).aligned
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact (l.created_connects h ⟨i, List.mem_range.mp hi⟩).aligned

/-- The complete executable source program contains only actual orthogonal segments. -/
theorem programFrom_aligned {w : Word} {a b : List Color} (D : w.OrthogonalDrawing a b)
    (st : Word.State) (hlen : st.wires.length = a.length) (y : ℕ)
    {r : Route} (hr : r ∈ programFrom w st y) : ∀ s ∈ r.path, s.AxisAligned := by
  induction D generalizing st y with
  | nil a => simp at hr
  | @cons sl w a b c layer rest ih =>
    let l : Layer := ⟨sl, st⟩
    have hl : l.HasDrawing := ⟨a, b, layer, hlen⟩
    rw [programFrom_cons] at hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      intro s hs
      obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
      exact Segment.translate_aligned (l.connections_aligned hl hr' s' hs') 0 y
    · exact ih (sl.run st) (drawn_after_length layer st hlen) (y + l.height) hr

/-- The actual refined route table supplied to the unit-cell layout stage. -/
def refinedProgram (w : Word) : List Route := (program w).map Route.refined

/-- Refining every source segment is part of the reduction's polynomial-time machine. -/
theorem refinedProgram_polyTime :
    ComputableInPolyTime refinedProgram encWord (encList encRoute) := by
  have hp := program_polyTime
  unfold refinedProgram
  fun_prop

/-- Different actual source edges still meet only at the refined actual vertex, including all new intermediate cells. -/
theorem refinedProgram_separated {w : Word} (hP : w.checkPlane = true) (hT : w.WellTyped [] [])
    {e f : ℕ} (hef : e ≠ f) {p : GridRouting.Point}
    (he : Route.Trace (refinedProgram w) e p) (hf : Route.Trace (refinedProgram w) f p) :
    ∃ q, VertexPointFrom w ⟨[], 0, []⟩ 0 q ∧ p = refinePoint q := by
  obtain ⟨re, hre, he, se, hse, hpe⟩ := he
  obtain ⟨rf, hrf, hf, sf, hsf, hpf⟩ := hf
  obtain ⟨re', hre', rfl⟩ := List.mem_map.mp hre
  obtain ⟨rf', hrf', rfl⟩ := List.mem_map.mp hrf
  obtain ⟨se', hse', rfl⟩ := List.mem_map.mp hse
  obtain ⟨sf', hsf', rfl⟩ := List.mem_map.mp hsf
  obtain ⟨D⟩ := Word.orthogonalDrawing hP hT
  have hsa := programFrom_aligned D ⟨[], 0, []⟩ rfl 0 hre' se' hse'
  have hta := programFrom_aligned D ⟨[], 0, []⟩ rfl 0 hrf' sf' hsf'
  have vertices (q : GridRouting.Point) (hq : se'.Contains q) (hq' : sf'.Contains q) :
      VertexPointFrom w ⟨[], 0, []⟩ 0 q :=
    programFrom_separated D ⟨[], 0, []⟩ rfl 0 hef
      ⟨re', hre', he, se', hse', hq⟩ ⟨rf', hrf', hf, sf', hsf', hq'⟩
  obtain ⟨q, hq, hq', hp⟩ := Segment.refined_intersection hsa hta
    (fun q r hq hq' hr hr' hn => (vertices q hq hq').eq_of_nearby (vertices r hr hr') hn) hpe hpf
  exact ⟨q, vertices q hq hq', hp⟩

end Plan
end PushPuzzle.PushFS.Reduction
