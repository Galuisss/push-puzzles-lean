/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionFootprint
public import PushS.FiniteRoutingGateClearance

/-! The actual narrow line action footprint avoids distant path, other-arm and core-tail walls. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

namespace PathSpec

theorem action_at (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w) (i : ℕ)
    (hi : i < P.segments.length)
    (p : Cell (Line.width w (Line.program w (segmentLength (P.line i).segment)
      ((P.line i).above != (P.line i).desiredSide))) (Line.height w))
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength (P.line i).segment)
      ((P.line i).above != (P.line i).desiredSide)) (P.line i).above (P.line i).last) :
    ∃ u, (segmentAt P.segments i).Contains u ∧
      Nearby (w+2) ((P.line i).actionWorld w hw p) (padding w+u.1,padding w+u.2) := by
  obtain ⟨u,hu,ha⟩ := (P.line i).action_footprint w hw (P.line_good w G i hi) p hp
  have hs := G.good _ (P.segment_mem i hi)
  exact ⟨u,trimmed_trace_subset _ hs.1 _ _
    (by have hf := startTrim_bound P.segments i; have hb := finishTrim_bound P.segments i
        have hl := hs.2.1; omega) hu,ha⟩

theorem action_ne_line_far (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : j < P.segments.length) (hij : i+1 < j ∨ j+1 < i)
    (p : Cell (Line.width w (Line.program w (segmentLength (P.line i).segment)
      ((P.line i).above != (P.line i).desiredSide))) (Line.height w))
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength (P.line i).segment)
      ((P.line i).above != (P.line i).desiredSide)) (P.line i).above (P.line i).last)
    (q : Cell ((PrimitiveCode.line (P.line j)).instanceOf w hw).width ((PrimitiveCode.line (P.line j)).instanceOf w hw).height)
    (hq : q ∈ ((PrimitiveCode.line (P.line j)).instanceOf w hw).board.walls) :
    (P.line i).actionWorld w hw p ≠ (PrimitiveCode.line (P.line j)).world w hw q := by
  obtain ⟨u,hu,ha⟩ := P.action_at w hw G i hi p hp
  obtain ⟨v,hv,hb⟩ := P.line_wall_at w hw G j hj q hq
  rcases hij with hij | hij
  · exact P.marks_ne w G i j hi hj hij (w+2) (w+1) (by unfold FiniteGeometry.origin; omega) hu hv ha hb
  · exact Ne.symm (P.marks_ne w G j i hj hi hij (w+1) (w+2) (by unfold FiniteGeometry.origin; omega) hv hu hb ha)

theorem action_ne_turn_far (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : P.hasTurn j) (hne : i ≠ j) (hne' : i ≠ j+1)
    (p : Cell (Line.width w (Line.program w (segmentLength (P.line i).segment)
      ((P.line i).above != (P.line i).desiredSide))) (Line.height w))
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength (P.line i).segment)
      ((P.line i).above != (P.line i).desiredSide)) (P.line i).above (P.line i).last)
    (q : Cell (FiniteTools.side w) (FiniteTools.side w)) :
    (P.line i).actionWorld w hw p ≠ (PrimitiveCode.turn (P.turn j)).world w hw q := by
  obtain ⟨u,hu,ha⟩ := P.action_at w hw G i hi p hp
  have hb := P.turn_wall_at w hw j q
  by_cases hij : i < j
  · rw [P.join_eq w G j hj.1] at hb
    exact P.marks_ne w G i (j+1) hi hj.1 (by omega) (w+2) (FiniteTools.radius w)
      (by unfold FiniteGeometry.origin FiniteTools.radius; omega) hu (P.start_contains w G (j+1) hj.1) ha hb
  · exact Ne.symm (P.marks_ne w G j i (by have := hj.1; omega) hi (by omega)
      (FiniteTools.radius w) (w+2) (by unfold FiniteGeometry.origin FiniteTools.radius; omega)
      (P.finish_contains w G j (by have := hj.1; omega)) hu hb ha)

end PathSpec

theorem different_arms_action_ne_wall (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (i j : Fin 3) (hij : i ≠ j) (n : ℕ) (hn : n < (armSpec w g i).segments.length)
    (p : Cell (Line.width w (Line.program w (segmentLength ((armSpec w g i).line n).segment)
      (((armSpec w g i).line n).above != ((armSpec w g i).line n).desiredSide))) (Line.height w))
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength ((armSpec w g i).line n).segment)
      (((armSpec w g i).line n).above != ((armSpec w g i).line n).desiredSide))
      ((armSpec w g i).line n).above ((armSpec w g i).line n).last)
    (c : PrimitiveCode) (hc : c ∈ (armSpec w g j).codes)
    (q : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height) (hq : q ∈ (c.instanceOf w hw).board.walls) :
    ((armSpec w g i).line n).actionWorld w hw p ≠ c.world w hw q := by
  obtain ⟨u,hu,ha⟩ := (armSpec w g i).action_at w hw (armSpec_geometry w g i) n hn p hp
  have hu' : ∃ s ∈ armRoute w g i, s.Contains u := ⟨_,(armSpec w g i).segment_mem n hn,hu⟩
  rcases (armSpec w g j).code_wall_trace w hw (armSpec_geometry w g j) c hc q hq with h | h
  · obtain ⟨v,hv,hb⟩ := h
    exact footprint_ne (w := w)
      (fun hh => armRoutes_separated_wide w g hij hu' hv (nearby_of_le (by omega) hh)) ha hb
  · obtain ⟨v,hv,hb⟩ := h
    apply Ne.symm
    exact footprint_ne (w := w)
      (fun hh => armRoute_tail_separated w g (Ne.symm hij) hv hu'
        (nearby_of_le (by unfold FiniteGeometry.origin FiniteTools.radius; omega) hh)) hb ha

end PushPuzzle.PushS.FiniteRouting
