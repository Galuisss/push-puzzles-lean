/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteLineMacros
public import PushS.FiniteLineFrame
public import PushFS.Isometry

/-! Vertical sweeps reuse the complete horizontal line macro by exact transposition. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteVerticalLineMacros

open PushFS FiniteLineMacros

variable {W H : ℕ}

/-- The same frontier inventory, with horizontal and vertical coordinates interchanged. -/
def boxes (L : Line H W) (fixed : Finset (Cell W H)) (frontier : ℕ) : Finset (Cell W H) :=
  fixed ∪ Finset.univ.image (fun i => Prod.swap (L.position frontier i))

structure Frame (L : Line H W) (B : Board W H) (fixed : Finset (Cell W H)) : Prop where
  fixed_floor : Disjoint fixed B.walls
  track_free : ∀ y, L.track y → Free B fixed (L.row, y)
  lane_free : ∀ y, L.laneSegment y → Free B fixed (L.lane, y)

private theorem free_transpose {B : Board W H} {fixed : Finset (Cell W H)} {p : Cell W H}
    (hp : Free B fixed p) :
    Free ((GridIsometry.transpose W H).board B)
      (fixed.map (GridIsometry.transpose W H).cells.toEmbedding) (Prod.swap p) := by
  simpa [Free, GridIsometry.board, GridIsometry.transpose] using hp

private theorem Frame.horizontal {L : Line H W} {B : Board W H} {fixed : Finset (Cell W H)}
    (F : Frame L B fixed) :
    L.Frame ((GridIsometry.transpose W H).board B)
      (fixed.map (GridIsometry.transpose W H).cells.toEmbedding) where
  fixed_floor := by simpa [GridIsometry.board, Finset.disjoint_map] using F.fixed_floor
  track_free y hy := free_transpose (F.track_free y hy)
  lane_free y hy := free_transpose (F.lane_free y hy)

private theorem boxes_transpose (L : Line H W) (fixed : Finset (Cell W H)) (frontier : ℕ) :
    (boxes L fixed frontier).map (GridIsometry.transpose W H).cells.toEmbedding =
      L.boxes (fixed.map (GridIsometry.transpose W H).cells.toEmbedding) frontier := by
  simp [boxes, Line.boxes, Finset.map_eq_image, Finset.image_union, Finset.image_image,
    GridIsometry.transpose, Function.comp_def]

/-- Push each vertical box upward, preserving the same exposed-lane hub. -/
theorem Frame.forward {L : Line H W} {B : Board W H} {fixed : Finset (Cell W H)}
    (F : Frame L B fixed) :
    Reachable B (some 1) ⟨(L.lane, L.hub), boxes L fixed 0⟩
      ⟨(L.lane, L.hub), boxes L fixed L.count⟩ := by
  apply ((GridIsometry.transpose W H).reachable_iff B (some 1) _ _).mp
  have hp : (GridIsometry.transpose W H).cells (L.lane, L.hub) = (L.hub, L.lane) := rfl
  simpa only [GridIsometry.state, boxes_transpose, hp] using F.horizontal.forward

/-- Push each vertical box downward in reverse order. -/
theorem Frame.backward {L : Line H W} {B : Board W H} {fixed : Finset (Cell W H)}
    (F : Frame L B fixed) :
    Reachable B (some 1) ⟨(L.lane, L.hub), boxes L fixed L.count⟩
      ⟨(L.lane, L.hub), boxes L fixed 0⟩ := by
  apply ((GridIsometry.transpose W H).reachable_iff B (some 1) _ _).mp
  have hp : (GridIsometry.transpose W H).cells (L.lane, L.hub) = (L.hub, L.lane) := rfl
  simpa only [GridIsometry.state, boxes_transpose, hp] using F.horizontal.backward

/-- Travel along the exposed vertical lane with the current frontier inventory fixed. -/
theorem Frame.lane_walk {L : Line H W} {B : Board W H} {fixed : Finset (Cell W H)}
    (F : Frame L B fixed) (j : ℕ) (a b : Fin H) (ha : L.laneSegment a) (hb : L.laneSegment b) :
    Reachable B (some 1) ⟨(L.lane, a), boxes L fixed j⟩ ⟨(L.lane, b), boxes L fixed j⟩ := by
  apply ((GridIsometry.transpose W H).reachable_iff B (some 1) _ _).mp
  have hpa : (GridIsometry.transpose W H).cells (L.lane, a) = (a, L.lane) := rfl
  have hpb : (GridIsometry.transpose W H).cells (L.lane, b) = (b, L.lane) := rfl
  simpa only [GridIsometry.state, boxes_transpose, hpa, hpb] using F.horizontal.lane_walk j a b ha hb

/-- A single vertical push reached through a specified adjacent parallel column. -/
theorem push_via_parallel_column {B : Board W H} {stock : Finset (Cell W H)}
    (hstock : Disjoint stock B.walls) (hub support src dst : Fin H) (lane row : Fin W)
    (entry d : Direction)
    (hentry : Adjacent entry (lane, support) (row, support))
    (hexit : Adjacent entry.opposite (row, src) (lane, src))
    (hax : Adjacent d (row, support) (row, src))
    (hxd : Adjacent d (row, src) (row, dst))
    (hsupport : Free B stock (row, support)) (hsource : (row, src) ∈ stock)
    (hdest : Free B stock (row, dst))
    (hlane : ∀ z : Fin H, min hub.val support.val ≤ z.val → z.val ≤ max hub.val support.val →
      Free B stock (lane, z))
    (hreturn : ∀ z : Fin H, min src.val hub.val ≤ z.val → z.val ≤ max src.val hub.val →
      Free B stock (lane, z)) :
    Reachable B (some 1) ⟨(lane, hub), stock⟩
      ⟨(lane, hub), insert (row, dst) (stock.erase (row, src))⟩ := by
  let e := GridIsometry.transpose W H
  have hfloor : Disjoint (stock.map e.cells.toEmbedding) (e.board B).walls := by
    simpa only [GridIsometry.board, Finset.disjoint_map] using hstock
  have he : Adjacent (e.directions entry) (support, lane) (support, row) :=
    (e.adjacent entry _ _).mpr hentry
  have hx : Adjacent (e.directions entry).opposite (src, row) (src, lane) := by
    have hdir : e.directions entry.opposite = (e.directions entry).opposite := by
      cases entry <;> rfl
    rw [← hdir]
    exact (e.adjacent entry.opposite _ _).mpr hexit
  have ha : Adjacent (e.directions d) (support, row) (src, row) :=
    (e.adjacent d _ _).mpr hax
  have hd : Adjacent (e.directions d) (src, row) (dst, row) :=
    (e.adjacent d _ _).mpr hxd
  have hmem : (src, row) ∈ stock.map e.cells.toEmbedding := by
    simpa [e, GridIsometry.transpose] using hsource
  have hr := push_via_parallel_row hfloor hub support src dst lane row (e.directions entry)
    (e.directions d) he hx ha hd (free_transpose hsupport) hmem (free_transpose hdest)
    (fun z hz hz' => free_transpose (hlane z hz hz'))
    (fun z hz hz' => free_transpose (hreturn z hz hz'))
  apply (e.reachable_iff B (some 1) _ _).mp
  have hh : e.cells (lane, hub) = (hub, lane) := rfl
  have hs : e.cells.toEmbedding (row, src) = (src, row) := rfl
  have hd' : e.cells.toEmbedding (row, dst) = (dst, row) := rfl
  simpa only [GridIsometry.state, Finset.map_insert, Finset.map_erase, hh, hs, hd'] using hr

end PushPuzzle.PushS.FiniteVerticalLineMacros
