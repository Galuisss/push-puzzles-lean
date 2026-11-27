/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.CompleteFlow
public import PushFS.Reduction.WireSelection
public import PushFS.Reduction.VertexQuery

/-! Every ordinary pixel of the actual checked source drawing selects one of the seven real physical wire cells. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL

namespace Plan

private theorem run_next_mono {w : Word} {a b : List Color} (D : w.OrthogonalDrawing a b)
    (st : Word.State) (hlen : st.wires.length=a.length) : st.next≤(Word.run w st).next := by
  induction D generalizing st with
  | nil => exact le_rfl
  | @cons sl w a b c layer rest ih =>
    let l : Layer := ⟨sl,st⟩
    have hl : l.HasDrawing := ⟨a,b,layer,hlen⟩
    have hh := ih (sl.run st) (drawn_after_length layer st hlen)
    change l.after.next≤(Word.run (sl::w) st).next at hh
    have he : l.before.next≤l.after.next := by rw [l.after_next hl]; omega
    exact he.trans hh

private theorem programFrom_edge_lt {w : Word} {a b : List Color} (D : w.OrthogonalDrawing a b)
    (st : Word.State) (hn : Numbered st) (hlen : st.wires.length=a.length) (y : ℕ)
    {r : Route} (hr : r ∈ programFrom w st y) : r.edge<(Word.run w st).next := by
  induction D generalizing st y with
  | nil => simp at hr
  | @cons sl w a b c layer rest ih =>
    let l : Layer := ⟨sl,st⟩
    have hl : l.HasDrawing := ⟨a,b,layer,hlen⟩
    rw [programFrom_cons] at hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hr
      exact (l.connection_edge_lt hn hl hr').trans_le
        (run_next_mono rest (sl.run st) (drawn_after_length layer st hlen))
    · exact ih (sl.run st) (l.after_numbered hn hl) (drawn_after_length layer st hlen) (y+l.height) hr

end Plan

namespace Raster

/-- A found ordinary owner is an actual finite edge of the original compiled NCL graph. -/
private theorem owner_edge_lt {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {p : GridRouting.Point} {e : ℕ} (he : owner (w,p)=some e) : e<w.compile.edgeCount := by
  obtain ⟨r,hr,hedge,_⟩ := owner_sound he
  obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hr
  obtain ⟨D⟩ := Word.orthogonalDrawing hP hT
  have hh := Plan.programFrom_edge_lt D ⟨[],0,[]⟩ ⟨by simp,by simp⟩ rfl 0 hr'
  change r'.edge=e at hedge
  rw [← hedge]
  exact hh

/-- The real source compiler's ordinary pixels have exactly the two physical ports of an actual selected glyph. -/
theorem wireAt_defined {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {p : GridRouting.Point} {e : ℕ} (he : owner (w,p)=some e) (hv : vertexAt (w,p)=none) :
    ∃ k,wireAt (w,(e,p))=some k := by
  let edge : Fin w.compile.edgeCount := ⟨e,owner_edge_lt hP hT he⟩
  obtain ⟨s,t,hs,ht,hf⟩ := Plan.complete_refined_flow hP hT edge
  have hp : HasPoint (Route.edgeSegments (Plan.refinedProgram w,e)) p :=
    (Route.edgeSegments_trace _ _ _).mpr (owner_sound he)
  have hv' := (vertexAt_none_iff w p).mp hv
  have hsource : p≠refinePoint s := fun hh=>hv' ⟨s,hs.vertex,hh⟩
  have htarget : p≠refinePoint t := fun hh=>hv' ⟨t,ht.vertex,hh⟩
  exact wireAt_of_flow hP hT hf hp hsource htarget

end Raster
end PushPuzzle.PushFS.Reduction
