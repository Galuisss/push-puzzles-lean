/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPathJunctions

/-! Actual inward boundary adjustment preserves all proved arm separation and joins. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

theorem armRoute_length (w : ℕ) (g : GateTileState) (role : Fin 3) :
    (armRoute w g role).length = (route w g.core.isAND (g.pattern,g.rotation,role)).length := by
  simp only [armRoute,List.length_mapIdx]

theorem armRoute_contains_getElem (w : ℕ) (g : GateTileState) (role : Fin 3) (i : ℕ)
    (hi : i < (armRoute w g role).length) {u : ℕ × ℕ}
    (hu : ((armRoute w g role)[i]).Contains u) :
    ((route w g.core.isAND (g.pattern,g.rotation,role))[i]'(by rwa [←armRoute_length])).Contains u := by
  have hi' : i < (route w g.core.isAND (g.pattern,g.rotation,role)).length := by rwa [←armRoute_length]
  have hg := route_segment_good w g.core.isAND (g.pattern,g.rotation,role)
    (List.getElem_mem hi')
  simp only [armRoute,List.getElem_mapIdx] at hu
  split_ifs at hu with hlast
  · have hbit := Bool.toNat_le (g.incoming.get role)
    have hz : ∀ d p, advance d p 0 = p := by intro d p; cases d <;> rfl
    apply segment_shrink_contains _ _ _ _ 0 (g.incoming.get role).toNat
      (segment_travels _ hg.1) (by have hl := hg.2.1; omega)
    simpa only [hz] using hu
  · exact hu

private theorem armRoute_trace_subset (w : ℕ) (g : GateTileState) (role : Fin 3) {u : ℕ × ℕ}
    (hu : ∃ s ∈ armRoute w g role, s.Contains u) :
    ∃ s ∈ route w g.core.isAND (g.pattern,g.rotation,role), s.Contains u := by
  obtain ⟨s,hs,hu⟩ := hu
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hs
  rw [←he] at hu
  exact ⟨_,List.getElem_mem (by rwa [←armRoute_length]),armRoute_contains_getElem w g role i hi hu⟩

theorem armRoute_tail_trace_subset (w : ℕ) (g : GateTileState) (role : Fin 3) {u : ℕ × ℕ}
    (hu : ∃ s ∈ (armRoute w g role).tail, s.Contains u) :
    ∃ s ∈ (route w g.core.isAND (g.pattern,g.rotation,role)).tail, s.Contains u := by
  obtain ⟨s,hs,hu⟩ := hu
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hs
  have hi' : i+1 < (armRoute w g role).length := by simp only [List.length_tail] at hi; omega
  rw [←he] at hu
  have hu' : ((armRoute w g role)[i+1]).Contains u := by simpa only [List.getElem_tail] using hu
  have hraw : i+1 < (route w g.core.isAND (g.pattern,g.rotation,role)).length := by rwa [←armRoute_length]
  exact ⟨_,List.getElem_mem_tail _ (by omega) hraw,armRoute_contains_getElem w g role (i+1) hi' hu'⟩

theorem armRoute_joined (w : ℕ) (g : GateTileState) (role : Fin 3) :
    (armRoute w g role).IsChain (fun s t => s.finish = t.start) := by
  apply List.isChain_iff_getElem.mpr
  intro i hi
  have hi' : i+1 < (route w g.core.isAND (g.pattern,g.rotation,role)).length := by
    simpa only [armRoute_length] using hi
  have h := (route_joined w g.core.isAND (g.pattern,g.rotation,role)).getElem i hi'
  simp only [armRoute,List.getElem_mapIdx]
  split_ifs with hlast hnext <;> omega

private theorem gap_restrict {s t a b : Segment} {margin : ℕ} (hgap : s.gapTest margin t = true)
    (ha : s.Contains a.start) (ha' : s.Contains a.finish)
    (hb : t.Contains b.start) (hb' : t.Contains b.finish) : a.gapTest margin b = true := by
  have ha := Segment.coordinate_bounds ha
  have ha' := Segment.coordinate_bounds ha'
  have hb := Segment.coordinate_bounds hb
  have hb' := Segment.coordinate_bounds hb'
  simp only [Segment.gapTest,decide_eq_true_eq] at *
  omega

private theorem segment_start_mem (s : Segment) (hs : s.start.1 = s.finish.1 ∨ s.start.2 = s.finish.2) :
    s.Contains s.start := by
  rcases hs with hx | hy
  · exact Or.inl ⟨hx,rfl,min_le_left _ _,le_max_left _ _⟩
  · exact Or.inr ⟨hy,rfl,min_le_left _ _,le_max_left _ _⟩

private theorem segment_finish_mem (s : Segment) (hs : s.start.1 = s.finish.1 ∨ s.start.2 = s.finish.2) :
    s.Contains s.finish := by
  rcases hs with hx | hy
  · exact Or.inl ⟨hx,hx.symm,min_le_right _ _,le_max_right _ _⟩
  · exact Or.inr ⟨hy,hy.symm,min_le_right _ _,le_max_right _ _⟩

theorem armRoute_nonadjacent_gap (w : ℕ) (g : GateTileState) (role : Fin 3)
    (i j : Fin (armRoute w g role).length) (hij : i.val+1 < j.val) :
    (segmentAt (armRoute w g role) i.val).gapTest (FiniteGeometry.origin w)
      (segmentAt (armRoute w g role) j.val) = true := by
  have hi : i.val < (route w g.core.isAND (g.pattern,g.rotation,role)).length := by simpa only [armRoute_length] using i.isLt
  have hj : j.val < (route w g.core.isAND (g.pattern,g.rotation,role)).length := by simpa only [armRoute_length] using j.isLt
  have hgap := route_nonadjacent_gap w g.core.isAND (g.pattern,g.rotation,role) ⟨i.val,hi⟩ ⟨j.val,hj⟩ hij
  have hgi := armRoute_good w g role _ (List.getElem_mem i.isLt)
  have hgj := armRoute_good w g role _ (List.getElem_mem j.isLt)
  simp only [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj] at hgap
  simp only [segmentAt,List.getD_eq_getElem _ _ i.isLt,List.getD_eq_getElem _ _ j.isLt]
  exact gap_restrict hgap
    (armRoute_contains_getElem w g role i.val i.isLt (segment_start_mem _ hgi.1))
    (armRoute_contains_getElem w g role i.val i.isLt (segment_finish_mem _ hgi.1))
    (armRoute_contains_getElem w g role j.val j.isLt (segment_start_mem _ hgj.1))
    (armRoute_contains_getElem w g role j.val j.isLt (segment_finish_mem _ hgj.1))

theorem armRoutes_separated_wide (w : ℕ) (g : GateTileState) {i j : Fin 3} (hij : i ≠ j)
    {p q : ℕ × ℕ} (hp : ∃ s ∈ armRoute w g i, s.Contains p)
    (hq : ∃ s ∈ armRoute w g j, s.Contains q) : ¬Nearby (2*w+6) p q :=
  routes_separated_wide w g.core.isAND g.pattern g.rotation hij
    (armRoute_trace_subset w g i hp) (armRoute_trace_subset w g j hq)

theorem armRoute_tail_separated (w : ℕ) (g : GateTileState) {i j : Fin 3} (hij : i ≠ j)
    {p q : ℕ × ℕ} (hp : ∃ s ∈ (armRoute w g i).tail, s.Contains p)
    (hq : ∃ s ∈ armRoute w g j, s.Contains q) : ¬Nearby (FiniteGeometry.origin w) p q :=
  route_tail_separated w g.core.isAND g.pattern g.rotation hij
    (armRoute_tail_trace_subset w g i hp) (armRoute_trace_subset w g j hq)

end PushPuzzle.PushS.FiniteRouting
