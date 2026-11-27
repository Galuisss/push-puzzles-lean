/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.CellPorts

/-! The actual refined source cells preserve the exterior player margin and gate diagonal clearance. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL Plan

private theorem Segment.refined_lower {s : Segment} {p : GridRouting.Point}
    (hp : s.refined.Contains p) :
    32≤p.1 ∧32≤p.2 := by
  have hb := s.refined.coordinate_bounds hp
  dsimp only [Segment.refined,refinePoint] at hb
  omega

private theorem Raster.trace_lower {w : Word} {e : ℕ} {p : GridRouting.Point}
    (hp : Route.Trace (refinedProgram w) e p) : 32≤p.1 ∧32≤p.2 := by
  obtain ⟨r,hr,_,s,hs,hp⟩ := hp
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
  obtain ⟨s,_,rfl⟩ := List.mem_map.mp hs
  exact s.refined_lower hp

theorem CellPlan.nonempty_lower {q : CellPlan.Source} {p : GridRouting.Point}
    (hc : CellPlan.cell (q,p)≠none) : 32≤p.1 ∧32≤p.2 := by
  cases hh : CellPlan.cell (q,p) with
  | none => exact (hc hh).elim
  | some c =>
    rcases c with ⟨v,g⟩|⟨e,k,a,b⟩
    · obtain ⟨hv,_⟩ := CellPlan.gate_sound hh
      obtain ⟨_,rfl⟩ := Raster.vertexAt_sound hv
      dsimp only [refinePoint]
      omega
    · obtain ⟨_,he,_,_,_⟩ := CellPlan.wire_sound hh
      exact Raster.trace_lower (Raster.owner_sound he)

theorem CellPlan.nonempty_bounds {q : CellPlan.Source} {p : GridRouting.Point}
    (hc : CellPlan.cell (q,p)≠none) : p.1<Raster.width q.1 ∧p.2<Raster.height q.1 := by
  cases hh : CellPlan.cell (q,p) with
  | none=>exact (hc hh).elim
  | some c=>
    rcases c with ⟨v,g⟩|⟨e,k,a,b⟩
    · obtain ⟨hv,_⟩:=CellPlan.gate_sound hh
      obtain ⟨hm,rfl⟩:=Raster.vertexAt_sound hv
      have hb:=Raster.vertex_bounds q.1 hm
      constructor <;> omega
    · obtain ⟨_,he,_,_,_⟩:=CellPlan.wire_sound hh
      have hb:=Raster.trace_bounds q.1 (Raster.owner_sound he)
      constructor <;> omega

/-- A refined straight segment within one coarse pixel of an old anchor lies on one of its two axes. -/
private theorem Segment.refined_near_anchor {s : Segment} {a p : GridRouting.Point}
    (hp : s.refined.Contains p)
    (hx : p.1≤(refinePoint a).1+1 ∧(refinePoint a).1≤p.1+1)
    (hy : p.2≤(refinePoint a).2+1 ∧(refinePoint a).2≤p.2+1) :
    p.1=(refinePoint a).1 ∨p.2=(refinePoint a).2 := by
  rcases hp with hp|hp
  · left
    dsimp only [Segment.refined,refinePoint] at hp hx ⊢
    omega
  · right
    dsimp only [Segment.refined,refinePoint] at hp hy ⊢
    omega

theorem Raster.trace_near_anchor {w : Word} {e : ℕ} {a p : GridRouting.Point}
    (hp : Route.Trace (refinedProgram w) e p)
    (hx : p.1≤(refinePoint a).1+1 ∧(refinePoint a).1≤p.1+1)
    (hy : p.2≤(refinePoint a).2+1 ∧(refinePoint a).2≤p.2+1) :
    p.1=(refinePoint a).1 ∨p.2=(refinePoint a).2 := by
  obtain ⟨r,hr,_,s,hs,hp⟩ := hp
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
  obtain ⟨s,_,rfl⟩ := List.mem_map.mp hs
  exact s.refined_near_anchor hp hx hy

/-- Two actual gate anchors within one source-grid step coincide. -/
theorem refinePoint_near_eq {a b : GridRouting.Point}
    (hx : (refinePoint a).1≤(refinePoint b).1+1 ∧(refinePoint b).1≤(refinePoint a).1+1)
    (hy : (refinePoint a).2≤(refinePoint b).2+1 ∧(refinePoint b).2≤(refinePoint a).2+1) :
    refinePoint a=refinePoint b := by
  apply Prod.ext <;> dsimp only [refinePoint] at * <;> omega

end PushPuzzle.PushFS.Reduction
