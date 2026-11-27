/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingHullJunctions

/-! Distinct actual path primitives have disjoint complete normal-travel intervals. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.PathSpec

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

theorem line_hull_at (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : i < P.segments.length) (l : (PrimitiveCode.line (P.line i)).Labels w)
    (a : ℕ × ℕ) (ha : ActorHull w hw (.line (P.line i)) l a) :
    ∃ u, (segmentAt P.segments i).Contains u ∧ Nearby 1 a (padding w+u.1,padding w+u.2) := by
  obtain ⟨u,hu,ha⟩ := line_hull_footprint w hw (P.line i) (P.line_good w G i hi) rfl l a ha
  refine ⟨u,?_,ha⟩
  have hs := G.good _ (P.segment_mem i hi)
  exact trimmed_trace_subset _ hs.1 _ _
    (by have hf := startTrim_bound P.segments i; have hb := finishTrim_bound P.segments i; have hl := hs.2.1; omega) hu

theorem turn_hull_at (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : P.hasTurn i) (l : Fin 2) (a : ℕ × ℕ) (ha : ActorHull w hw (.turn (P.turn i)) l a) :
    Nearby 2 a (padding w+(segmentAt P.segments i).finish.1,padding w+(segmentAt P.segments i).finish.2) :=
  turn_hull_footprint w hw (P.turn i) (P.turn_perpendicular w G i hi) l a ha

private theorem lines_hulls_apart (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : j < P.segments.length) (hij : i < j) :
    HullsApart w hw (.line (P.line i)) (.line (P.line j)) := by
  by_cases he : j = i+1
  · subst j
    by_cases ht : P.hasTurn i
    · exact perpendicular_hull_lines_apart w hw _ _ _ (P.junction_contract w G i ht) rfl
    · exact collinear_hulls_apart w hw _ _ (P.collinear_contract w G i hj ht) rfl
  · intro l r a b ha hb
    obtain ⟨u,hu,ha⟩ := P.line_hull_at w hw G i hi l a ha
    obtain ⟨v,hv,hb⟩ := P.line_hull_at w hw G j hj r b hb
    exact P.marks_ne w G i j hi hj (by omega) 1 1 (by unfold FiniteGeometry.origin; omega) hu hv ha hb

private theorem line_turn_hulls_apart (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : P.hasTurn j) :
    HullsApart w hw (.line (P.line i)) (.turn (P.turn j)) := by
  by_cases he : i = j
  · subst i
    exact incoming_turn_hulls_apart w hw _ _ _ (P.junction_contract w G j hj) rfl
  by_cases he' : i = j+1
  · subst i
    exact outgoing_turn_hulls_apart w hw _ _ _ (P.junction_contract w G j hj)
  intro l r a b ha hb
  by_cases hij : i < j
  · obtain ⟨u,hu,ha⟩ := P.line_hull_at w hw G i hi l a ha
    have hb := P.turn_hull_at w hw G j hj r b hb
    rw [P.join_eq w G j hj.1] at hb
    exact P.marks_ne w G i (j+1) hi hj.1 (by omega) 1 2 (by unfold FiniteGeometry.origin; omega)
      hu (P.start_contains w G (j+1) hj.1) ha hb
  · obtain ⟨v,hv,hb'⟩ := P.line_hull_at w hw G i hi l a ha
    have ha' := P.turn_hull_at w hw G j hj r b hb
    exact Ne.symm (P.marks_ne w G j i (by omega) hi (by omega) 2 1
      (by unfold FiniteGeometry.origin; omega) (P.finish_contains w G j (by omega)) hv ha' hb')

private theorem turns_hulls_apart (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : P.hasTurn i) (hj : P.hasTurn j) (hij : i < j) :
    HullsApart w hw (.turn (P.turn i)) (.turn (P.turn j)) := by
  intro l r a b ha hb
  have hil := hi.1
  have hjl := hj.1
  have ha' := P.turn_hull_at w hw G i hi l a ha
  have hb' := P.turn_hull_at w hw G j hj r b hb
  rw [P.join_eq w G j hj.1] at hb'
  exact P.marks_ne w G i (j+1) (by omega) hj.1 (by omega) 2 2
    (by unfold FiniteGeometry.origin; omega) (P.finish_contains w G i (by omega))
    (P.start_contains w G (j+1) hj.1) ha' hb'

private theorem block_hulls_pairwise (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : i < P.segments.length) : (P.block i).Pairwise (HullsApart w hw) := by
  by_cases ht : P.hasTurn i
  · simp only [block,ht,↓reduceIte,List.singleton_append]
    apply List.pairwise_cons.mpr
    refine ⟨?_,by simp⟩
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact P.line_turn_hulls_apart w hw G i i hi ht
  · simp only [block,ht,↓reduceIte,List.append_nil,List.pairwise_singleton]

private theorem blocks_hulls_apart (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : j < P.segments.length) (hij : i < j)
    (c : PrimitiveCode) (hc : c ∈ P.block i) (d : PrimitiveCode) (hd : d ∈ P.block j) :
    HullsApart w hw c d := by
  rcases (P.mem_block i c).mp hc with rfl | ⟨hti,rfl⟩ <;>
    rcases (P.mem_block j d).mp hd with rfl | ⟨htj,rfl⟩
  · exact P.lines_hulls_apart w hw G i j hi hj hij
  · exact P.line_turn_hulls_apart w hw G i j hi htj
  · intro l r a b ha hb
    exact Ne.symm (P.line_turn_hulls_apart w hw G j i hj hti r l b a hb ha)
  · exact P.turns_hulls_apart w hw G i j hti htj hij

theorem codes_hulls_pairwise (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w) :
    P.codes.Pairwise (HullsApart w hw) := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun i hi => P.block_hulls_pairwise w hw G i (List.mem_range.mp hi),?_⟩
  apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range
  intro i j hi hj hij
  exact P.blocks_hulls_apart w hw G i j (List.mem_range.mp hi) (List.mem_range.mp hj) hij

end PushPuzzle.PushS.FiniteRouting.PathSpec
