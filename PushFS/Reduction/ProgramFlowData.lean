/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.LayerFlow
public import PushFS.Reduction.CompletePaths

/-! Exact named instruction composition, disappearance and boundary fibers of the actual source word. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL

private theorem Route.edgeSegments_empty_of_trace_absent (rs : List Route) (e : ℕ)
    (ha : ∀ p,¬Route.Trace rs e p) (halign : ∀ r∈rs,∀ s∈r.path,s.AxisAligned) : edgeSegments (rs,e)=[] := by
  cases hh : edgeSegments (rs,e) with
  | nil => rfl
  | cons s ss =>
    have hs : s∈edgeSegments (rs,e) := by rw [hh]; simp
    obtain ⟨r,hr,he,hs⟩ := (mem_edgeSegments rs e s).mp hs
    have hp := Segment.contains_of_bounds (halign r hr s hs)
      ⟨min_le_left _ _,le_max_left _ _,min_le_left _ _,le_max_left _ _⟩
    exact False.elim (ha s.start ⟨r,hr,he,s,hs,hp⟩)

namespace Plan

theorem InputEndpoint.vertex {w : Word} {st : Word.State} {y e : ℕ} {p : GridRouting.Point}
    (h : InputEndpoint w st y e p) : VertexPointFrom w st y p := by
  induction h with
  | here sl w st y _ => exact VertexPointFrom.here sl w st y
  | later _ ih => exact VertexPointFrom.later ih

theorem OutputEndpoint.vertex {w : Word} {st : Word.State} {y e : ℕ} {p : GridRouting.Point}
    (h : OutputEndpoint w st y e p) : VertexPointFrom w st y p := by
  induction h with
  | here sl w st y _ => exact VertexPointFrom.here sl w st y
  | later _ ih => exact VertexPointFrom.later ih

theorem programFrom_edgeSegments_cons (sl : Slice) (w : Word) (st : Word.State) (y e : ℕ) :
    Route.edgeSegments (programFrom (sl::w) st y,e)=
      (Route.edgeSegments ((Layer.mk sl st).connections,e)).map (fun s=>s.translate 0 y)++
        Route.edgeSegments (programFrom w (sl.run st) (y+(Layer.mk sl st).height),e) := by
  rw [programFrom_cons,Route.edgeSegments_append,Route.edgeSegments_translate]

/-- An allocated edge absent from the live cut has no later emitted instruction. -/
theorem programFrom_segments_absent {w : Word} {a b : List Color} (D : w.OrthogonalDrawing a b)
    (st : Word.State) (hn : Numbered st) (hlen : st.wires.length=a.length) {e : ℕ}
    (he : e<st.next) (ha : e∉st.wires) (y : ℕ) : Route.edgeSegments (programFrom w st y,e)=[] := by
  apply Route.edgeSegments_empty_of_trace_absent
  · exact fun p=>programFrom_absent D st hn hlen he ha y p
  · exact fun r hr s hs=>programFrom_aligned D st hlen y hr s hs

/-- A real named active edge has only its own endpoint on the first cut row. -/
theorem programFrom_named_top {w : Word} {a b : List Color} (D : w.OrthogonalDrawing a b)
    (st : Word.State) (hn : Numbered st) (hlen : st.wires.length=a.length) (y : ℕ)
    (i : Fin st.wires.length) {e : ℕ} (he : st.wires.getD i.val 0=e) {p : GridRouting.Point}
    (hp : HasPoint (Route.edgeSegments (programFrom w st y,e)) p) (hy : p.2=y) : p=(4*i.val,y) := by
  obtain ⟨j,hx,hj⟩ := programFrom_top D st hlen y ((Route.edgeSegments_trace _ _ _).mp hp) hy
  have hji := hn.getD_injective j.isLt i.isLt (hj.trans he.symm)
  apply Prod.ext
  · simpa only [hji] using hx
  · exact hy

end Plan
end PushPuzzle.PushFS.Reduction
