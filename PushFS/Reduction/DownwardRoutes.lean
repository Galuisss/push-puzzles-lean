/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.DirectedRaster

/-! The actual source drawing never travels north, including every new refined unit arc. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL

def Segment.Downward (s : Segment) : Prop := s.start.2≤s.finish.2

private theorem segments_downward {p q : GridRouting.Point} (r : GridRouting.Path p q) :
    ∀ s∈segments r,s.Downward := by
  induction r with
  | horizontal => intro s hs; cases List.mem_singleton.mp hs; exact le_rfl
  | vertical _ _ _ h => intro s hs; cases List.mem_singleton.mp hs; exact h
  | comp r t ihr iht =>
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact ihr s hs
    · exact iht s hs

private theorem Connects.downward {ss : List Segment} {p q : GridRouting.Point}
    (h : Connects ss p q) :
    ∀ s∈ss,s.Downward := by
  obtain ⟨r,rfl⟩ := h
  exact segments_downward r

private theorem Segment.translate_downward {s : Segment} (h : s.Downward) (dx dy : ℕ) :
    (s.translate dx dy).Downward := by
  dsimp [Segment.Downward,Segment.translate] at *
  omega

private theorem Segment.refined_downward {s : Segment} (h : s.Downward) : s.refined.Downward := by
  dsimp [Segment.Downward,Segment.refined,refinePoint] at *
  omega

namespace Plan

private theorem Layer.connections_downward {l : Layer} (h : l.HasDrawing) {r : Route}
    (hr : r ∈ l.connections) :
    ∀ s∈r.path,s.Downward := by
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    exact (l.incoming_connects h ⟨i,List.mem_range.mp hi⟩).downward
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    exact (l.created_connects h ⟨i,List.mem_range.mp hi⟩).downward

private theorem programFrom_downward {w : Word} {a b : List Color} (D : w.OrthogonalDrawing a b)
    (st : Word.State) (hlen : st.wires.length=a.length) (y : ℕ)
    {r : Route} (hr : r ∈ programFrom w st y) : ∀ s∈r.path,s.Downward := by
  induction D generalizing st y with
  | nil => simp at hr
  | @cons sl w a b c layer rest ih =>
    let l : Layer := ⟨sl,st⟩
    have hl : l.HasDrawing := ⟨a,b,layer,hlen⟩
    rw [programFrom_cons] at hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hr
      intro s hs
      obtain ⟨s',hs',rfl⟩ := List.mem_map.mp hs
      exact Segment.translate_downward (l.connections_downward hl hr' s' hs') 0 y
    · exact ih (sl.run st) (drawn_after_length layer st hlen) (y+l.height) hr

/-- Actual emitted refined instructions retain the source's downward orientation. -/
private theorem refinedProgram_downward {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {r : Route} (hr : r ∈ refinedProgram w) {s : Segment} (hs : s ∈ r.path) : s.Downward := by
  obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hr
  obtain ⟨s',hs',rfl⟩ := List.mem_map.mp hs
  obtain ⟨D⟩ := Word.orthogonalDrawing hP hT
  exact Segment.refined_downward (programFrom_downward D ⟨[],0,[]⟩ rfl 0 hr' s' hs')

end Plan

namespace Raster

theorem outgoing_north_false {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (e : ℕ) (p : GridRouting.Point) : outgoing .north (w,(e,p))=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨r,hr,_,s,hs,h⟩ := (outgoing_correct .north w e p).mp h
  have hh := Plan.refinedProgram_downward hP hT hr hs
  dsimp [Segment.Arc,Segment.Downward] at h hh
  omega

theorem incoming_south_false {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (e : ℕ) (p : GridRouting.Point) : incoming .south (w,(e,p))=false :=
  outgoing_north_false hP hT e (p.1,p.2+1)

end Raster
end PushPuzzle.PushFS.Reduction
