/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPathInventory

/-! Actual different-arm inventories have unique actors and avoid one another's emitted walls. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteTools.turnWalls

namespace PathSpec

theorem segment_mem_tail (P : PathSpec) (i : ℕ) (hi : i < P.segments.length) (hp : 0 < i) :
    segmentAt P.segments i ∈ P.segments.tail := by
  rw [segmentAt,List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem_tail _ (by omega) hi

theorem code_actor_trace (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (c : PrimitiveCode) (hc : c ∈ P.codes) (goal : Bool) (l : c.Labels w) :
    ∃ u, (∃ s ∈ P.segments, s.Contains u) ∧
      Nearby 2 (c.actor w hw goal l) (padding w+u.1,padding w+u.2) := by
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases (P.mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · obtain ⟨u,hu,ha⟩ := P.line_actor_at w hw G i hi' goal l
    exact ⟨u,⟨_,P.segment_mem i hi',hu⟩,nearby_of_le (by omega) ha⟩
  · exact ⟨_,⟨_,P.segment_mem i hi',P.finish_contains w G i hi'⟩,P.turn_actor_at w hw G i ht goal l⟩

/-- Every wall mark lies on a narrow strip, or in a turn window on the noninitial path suffix. -/
theorem code_wall_trace (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (c : PrimitiveCode) (hc : c ∈ P.codes)
    (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height)
    (hp : p ∈ (c.instanceOf w hw).board.walls) :
    (∃ u, (∃ s ∈ P.segments, s.Contains u) ∧
      Nearby (w+1) (c.world w hw p) (padding w+u.1,padding w+u.2)) ∨
    (∃ u, (∃ s ∈ P.segments.tail, s.Contains u) ∧
      Nearby (FiniteTools.radius w) (c.world w hw p) (padding w+u.1,padding w+u.2)) := by
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases (P.mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · obtain ⟨u,hu,ha⟩ := P.line_wall_at w hw G i hi' p hp
    exact Or.inl ⟨u,⟨_,P.segment_mem i hi',hu⟩,ha⟩
  · have ha := P.turn_wall_at w hw i p
    rw [P.join_eq w G i ht.1] at ha
    exact Or.inr ⟨_,⟨_,P.segment_mem_tail (i+1) ht.1 (by omega),P.start_contains w G (i+1) ht.1⟩,ha⟩

end PathSpec

theorem different_arms_actor_apart (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (i j : Fin 3) (hij : i ≠ j) (c d : PrimitiveCode)
    (hc : c ∈ (armSpec w g i).codes) (hd : d ∈ (armSpec w g j).codes) : ActorsApart w hw c d := by
  intro goal l r
  obtain ⟨u,hu,ha⟩ := (armSpec w g i).code_actor_trace w hw (armSpec_geometry w g i) c hc goal l
  obtain ⟨v,hv,hb⟩ := (armSpec w g j).code_actor_trace w hw (armSpec_geometry w g j) d hd goal r
  apply footprint_ne (w := w) (m := 2) (n := 2) _ ha hb
  intro hn
  exact armRoutes_separated_wide w g hij hu hv (nearby_of_le (by omega) hn)

theorem different_arms_wall_clear (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (i j : Fin 3) (hij : i ≠ j) (c d : PrimitiveCode)
    (hc : c ∈ (armSpec w g i).codes) (hd : d ∈ (armSpec w g j).codes) : ActorWallsClear w hw c d := by
  intro goal l p hp
  obtain ⟨u,hu,ha⟩ := (armSpec w g i).code_actor_trace w hw (armSpec_geometry w g i) c hc goal l
  rcases (armSpec w g j).code_wall_trace w hw (armSpec_geometry w g j) d hd p hp with h | h
  · obtain ⟨v,hv,hb⟩ := h
    apply footprint_ne (w := w) (m := 2) (n := w+1) _ ha hb
    intro hn
    exact armRoutes_separated_wide w g hij hu hv (nearby_of_le (by omega) hn)
  · obtain ⟨v,hv,hb⟩ := h
    apply Ne.symm
    apply footprint_ne (w := w) (m := FiniteTools.radius w) (n := 2) _ hb ha
    intro hn
    exact armRoute_tail_separated w g (Ne.symm hij) hv hu
      (nearby_of_le (by unfold FiniteTools.radius FiniteGeometry.origin; omega) hn)

end PushPuzzle.PushS.FiniteRouting
