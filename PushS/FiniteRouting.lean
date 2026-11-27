/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGeometry
public import PushFS.Reduction.PortAnnulus
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Chain

/-! Linear-scale annular routes for the parameterized finite-force gate cores. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

abbrev Key := PortAnnulus.Key

/-- Route spacing leaves room for all width-`w` tools and their walking margins. -/
def spacing (w : ℕ) : ℕ := 1000 * (w+3)

/-- Translation of the unchanged finite core into the annulus's central square. -/
def coreOffset (w : ℕ) : ℕ := 24900 * (w+3)

/-- The complete annular routing tile, including its boundary anchors. -/
def side (w : ℕ) : ℕ := 50 * spacing w + 1

def scalePoint (factor : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (factor*p.1, factor*p.2)

def scaleSegment (factor : ℕ) (s : Segment) : Segment :=
  ⟨scalePoint factor s.start, scalePoint factor s.finish⟩

theorem spacing_pos (w : ℕ) : 0 < spacing w := by unfold spacing; omega

/-- Positive scaling preserves the exact outward port direction. -/
private theorem scalePoint_runs {factor : ℕ} (hf : 0 < factor) {d : Direction}
    {p q : ℕ × ℕ} (h : PortAnnulus.Runs d p q) :
    PortAnnulus.Runs d (scalePoint factor p) (scalePoint factor q) := by
  cases d <;> simp only [PortAnnulus.Runs, scalePoint] at * <;>
    exact ⟨congrArg (factor * ·) h.1, (Nat.mul_lt_mul_left hf).mpr h.2⟩

/-- A checked interval gap scales by the same factor as the route. -/
theorem scaleSegment_gap {factor margin : ℕ} (hf : 0 < factor) {s t : Segment}
    (h : s.gapTest margin t = true) :
    (scaleSegment factor s).gapTest (factor*margin) (scaleSegment factor t) = true := by
  simp only [Segment.gapTest, decide_eq_true_eq] at h ⊢
  simp only [scaleSegment, scalePoint, Nat.mul_min_mul_left, Nat.mul_max_mul_left]
  rcases h with h | h | h | h
  · exact Or.inl (by simpa only [Nat.mul_add] using (Nat.mul_lt_mul_left hf).mpr h)
  · exact Or.inr (Or.inl (by simpa only [Nat.mul_add] using (Nat.mul_lt_mul_left hf).mpr h))
  · exact Or.inr (Or.inr (Or.inl (by simpa only [Nat.mul_add] using (Nat.mul_lt_mul_left hf).mpr h)))
  · exact Or.inr (Or.inr (Or.inr (by simpa only [Nat.mul_add] using (Nat.mul_lt_mul_left hf).mpr h)))

/-- Actual waypoints obtained by scaling the already checked cyclic port table. -/
def vertices (w : ℕ) (q : Key) : List (ℕ × ℕ) :=
  (PortAnnulus.vertices q).map (scalePoint (spacing w))

/-- Every scaled instruction keeps its original order and both exact endpoints. -/
def curve (w : ℕ) (q : Key) : List Segment :=
  (PortAnnulus.curve q).map (scaleSegment (spacing w))

private theorem vertices_length (w : ℕ) (q : Key) :
    (vertices w q).length = (PortAnnulus.vertices q).length := List.length_map _

theorem curve_length (w : ℕ) (q : Key) :
    (curve w q).length = (PortAnnulus.curve q).length := List.length_map _

theorem endpoints (w : ℕ) (q : Key) :
    2 ≤ (vertices w q).length ∧
      (vertices w q).headD (0,0) = scalePoint (spacing w) (PortAnnulus.innerPoint q.2.2) ∧
      (vertices w q).getLastD (0,0) =
        scalePoint (spacing w) (PortAnnulus.outerPoint (PortAnnulus.outerDirection q)) ∧
      PortAnnulus.Runs (PortAnnulus.innerDirection q.2.2)
        (scalePoint (spacing w) (PortAnnulus.innerPoint q.2.2)) ((vertices w q).getD 1 (0,0)) ∧
      PortAnnulus.Runs (PortAnnulus.outerDirection q)
        ((vertices w q).getD ((vertices w q).length-2) (0,0))
        (scalePoint (spacing w) (PortAnnulus.outerPoint (PortAnnulus.outerDirection q))) := by
  obtain ⟨hn, hhead, hlast, hfirst, hfinish⟩ := PortAnnulus.endpoints q
  have h0 : scalePoint (spacing w) (0,0) = (0,0) := by simp [scalePoint]
  have hhead' := @List.headD_map _ _ (scalePoint (spacing w)) (PortAnnulus.vertices q) (0,0)
  have hlast' := @List.getLastD_map _ _ (scalePoint (spacing w)) (PortAnnulus.vertices q) (0,0)
  have hfirst' := @List.getD_map _ _ (PortAnnulus.vertices q) (0,0) 1 (scalePoint (spacing w))
  have hfinish' := @List.getD_map _ _ (PortAnnulus.vertices q) (0,0)
    ((PortAnnulus.vertices q).length-2) (scalePoint (spacing w))
  simp only [h0, hhead, hlast] at hhead' hlast' hfirst' hfinish'
  refine ⟨by simpa only [vertices_length] using hn, hhead', hlast', ?_, ?_⟩
  · rw [show (vertices w q).getD 1 (0,0) =
      scalePoint (spacing w) ((PortAnnulus.vertices q).getD 1 (0,0)) from hfirst']
    exact scalePoint_runs (spacing_pos w) hfirst
  · rw [vertices_length]
    rw [show (vertices w q).getD ((PortAnnulus.vertices q).length-2) (0,0) =
      scalePoint (spacing w) ((PortAnnulus.vertices q).getD ((PortAnnulus.vertices q).length-2) (0,0))
      from hfinish']
    exact scalePoint_runs (spacing_pos w) hfinish

private def gapCheck (pattern rotation i j : Fin 3) : Bool :=
  (PortAnnulus.curve (pattern,rotation,i)).all fun s =>
    (PortAnnulus.curve (pattern,rotation,j)).all fun t => s.gapTest 1 t

private def coreCheck (q : Key) : Bool :=
  (PortAnnulus.curve q).all fun s => decide
    (max s.start.1 s.finish.1 ≤ 20 ∨ 30 ≤ min s.start.1 s.finish.1 ∨
      max s.start.2 s.finish.2 ≤ 20 ∨ 30 ≤ min s.start.2 s.finish.2)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem gap_checked : ∀ pattern rotation i j : Fin 3,
    i ≠ j → gapCheck pattern rotation i j = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem core_checked : ∀ q : Key, coreCheck q = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem source_joined : ∀ q : Key,
    (PortAnnulus.curve q).IsChain (fun s t => s.finish = t.start) := by decide +kernel

/-- Every scaled segment ends at the next segment's literal start cell. -/
theorem joined (w : ℕ) (q : Key) :
    (curve w q).IsChain (fun s t => s.finish = t.start) := by
  apply List.isChain_map_of_isChain (scaleSegment (spacing w)) _ (source_joined q)
  intro s t hst
  exact congrArg (scalePoint (spacing w)) hst

/-- Each actual straight fragment has length at least the full routing spacing. -/
theorem segment_length (w : ℕ) (q : Key) {s : Segment} (hs : s ∈ curve w q) :
    (s.start.1 = s.finish.1 ∧ min s.start.2 s.finish.2 + spacing w ≤ max s.start.2 s.finish.2) ∨
      (s.start.2 = s.finish.2 ∧ min s.start.1 s.finish.1 + spacing w ≤ max s.start.1 s.finish.1) := by
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  have hh := PortAnnulus.segment_shape q hs'
  by_cases hx : s'.start.1 = s'.finish.1
  · have hy : s'.start.2 ≠ s'.finish.2 := fun hy => hh.1 (Prod.ext hx hy)
    have hlen : min s'.start.2 s'.finish.2 + 1 ≤ max s'.start.2 s'.finish.2 := by omega
    refine Or.inl ⟨congrArg (spacing w * ·) hx, ?_⟩
    simpa only [scaleSegment, scalePoint, Nat.mul_min_mul_left, Nat.mul_max_mul_left,
      Nat.mul_add, Nat.mul_one] using Nat.mul_le_mul_left (spacing w) hlen
  · have hy := hh.2.1.resolve_left hx
    have hlen : min s'.start.1 s'.finish.1 + 1 ≤ max s'.start.1 s'.finish.1 := by omega
    refine Or.inr ⟨congrArg (spacing w * ·) hy, ?_⟩
    simpa only [scaleSegment, scalePoint, Nat.mul_min_mul_left, Nat.mul_max_mul_left,
      Nat.mul_add, Nat.mul_one] using Nat.mul_le_mul_left (spacing w) hlen

/-- Different real port curves retain a full `spacing w` separation. -/
theorem separated (w : ℕ) (pattern rotation : Fin 3) {i j : Fin 3} (hij : i ≠ j)
    {p q : ℕ × ℕ} (hp : ∃ s ∈ curve w (pattern,rotation,i), s.Contains p)
    (hq : ∃ t ∈ curve w (pattern,rotation,j), t.Contains q) :
    ¬Nearby (spacing w) p q := by
  obtain ⟨s, hs, hp⟩ := hp
  obtain ⟨t, ht, hq⟩ := hq
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
  have hchecked := gap_checked pattern rotation i j hij
  have hgap := List.all_eq_true.mp (List.all_eq_true.mp hchecked s' hs') t' ht'
  have hh := scaleSegment_gap (spacing_pos w) hgap
  simp only [Nat.mul_one] at hh
  exact Segment.not_nearby_of_gap hh hp hq

/-- Every real route point lies within the explicit routing tile. -/
theorem trace_bounded (w : ℕ) (q : Key) {p : ℕ × ℕ}
    (hp : ∃ s ∈ curve w q, s.Contains p) :
    p.1 < side w ∧ p.2 < side w := by
  obtain ⟨s, hs, hp⟩ := hp
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  have hh := PortAnnulus.segment_shape q hs'
  have hb := Segment.coordinate_bounds hp
  have h1 := Nat.mul_le_mul_left (spacing w) hh.2.2.1
  have h2 := Nat.mul_le_mul_left (spacing w) hh.2.2.2.1
  have h3 := Nat.mul_le_mul_left (spacing w) hh.2.2.2.2.1
  have h4 := Nat.mul_le_mul_left (spacing w) hh.2.2.2.2.2
  simp only [scaleSegment, scalePoint] at hb
  dsimp [side]
  rw [Nat.mul_comm (spacing w) 50] at h1 h2 h3 h4
  omega

/-- The scaled annulus leaves the whole unchanged core, with a linear walking margin, clear. -/
theorem avoids_core (w : ℕ) (q : Key) {p r : ℕ × ℕ}
    (hp : ∃ s ∈ curve w q, s.Contains p)
    (hrx : coreOffset w ≤ r.1 ∧ r.1 < coreOffset w + FiniteGeometry.side w)
    (hry : coreOffset w ≤ r.2 ∧ r.2 < coreOffset w + FiniteGeometry.side w) :
    ¬Nearby (FiniteGeometry.origin w) p r := by
  obtain ⟨s, hs, hp⟩ := hp
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  have hh := of_decide_eq_true (List.all_eq_true.mp (core_checked q) s' hs')
  have hb := Segment.coordinate_bounds hp
  simp only [scaleSegment, scalePoint, Nat.mul_min_mul_left, Nat.mul_max_mul_left] at hb
  rcases hh with hh | hh | hh | hh
  all_goals
    have hh' := Nat.mul_le_mul_left (spacing w) hh
    dsimp [coreOffset, spacing, FiniteGeometry.side, FiniteGeometry.origin] at *
    unfold Nearby
    omega

end PushPuzzle.PushS.FiniteRouting
