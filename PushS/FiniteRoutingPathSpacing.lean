/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingSpacing
public import PushS.FiniteRoutingPathInventory

/-! Every actual path has sparse complete normal inventories, including shared-tool seams. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side

def ActorsSparse (w : ℕ) (hw : 2 ≤ w) (c e : PrimitiveCode) : Prop :=
  ∀ (goal : Bool) (l : c.Labels w) (r : e.Labels w) (d : Direction),
    ¬Travels d (c.actor w hw goal l) (e.actor w hw goal r) 1

private theorem ActorsSparse.symm {w : ℕ} {hw : 2 ≤ w} {c e : PrimitiveCode}
    (h : ActorsSparse w hw c e) :
    ActorsSparse w hw e c := by
  intro goal l r d ha
  exact h goal r l d.opposite (travels_one_reverse ha)

namespace PathSpec

private theorem marks_not_adjacent (P : PathSpec) (w : ℕ) (G : P.Geometry w) (i j : ℕ)
    (hi : i < P.segments.length) (hj : j < P.segments.length) (hij : i+1 < j)
    (m n : ℕ) (hm : m+n+1 ≤ FiniteGeometry.origin w) {u v a b : ℕ × ℕ}
    (hu : (segmentAt P.segments i).Contains u) (hv : (segmentAt P.segments j).Contains v)
    (ha : Nearby m a (padding w+u.1,padding w+u.2))
    (hb : Nearby n b (padding w+v.1,padding w+v.2)) (d : Direction) : ¬Travels d a b 1 := by
  have hs : ¬Nearby 1 a b := footprint_not_nearby (w := w)
    (fun h => Segment.not_nearby_of_gap (G.gap ⟨i,hi⟩ ⟨j,hj⟩ hij) hu hv (nearby_of_le hm h)) ha hb
  exact fun h => hs (travels_one_nearby h)

private theorem lines_actor_sparse (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : j < P.segments.length) (hij : i < j) :
    ActorsSparse w hw (.line (P.line i)) (.line (P.line j)) := by
  intro goal l r d
  by_cases he : j = i+1
  · subst j
    by_cases ht : P.hasTurn i
    · have hc := P.junction_contract w G i ht
      obtain ⟨m,hm,he⟩ := incoming_line_actor_ray w hw _ _ hc.incoming_good hc.incoming_last
        hc.incoming_direction hc.incoming_finish goal l
      obtain ⟨n,hn,hf⟩ := outgoing_line_actor_ray w hw _ _ hc.outgoing_good hc.outgoing_first
        hc.outgoing_direction hc.outgoing_start goal r
      rw [he,hf]
      exact perpendicular_rays_sparse w _ _ hc.perpendicular _ m n (by omega) (by omega) d
    · have hc := P.collinear_contract w G i hj ht
      exact collinear_actor_sparse w hw _ _ hc.first_good hc.next_good hc.next_first hc.directions hc.joined
        rfl rfl goal l r d
  · obtain ⟨u,hu,ha⟩ := P.line_actor_at w hw G i hi goal l
    obtain ⟨v,hv,hb⟩ := P.line_actor_at w hw G j hj goal r
    exact P.marks_not_adjacent w G i j hi hj (by omega) 1 1
      (by unfold FiniteGeometry.origin; omega) hu hv ha hb d

private theorem line_turn_sparse (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : P.hasTurn j) :
    ActorsSparse w hw (.line (P.line i)) (.turn (P.turn j)) := by
  have hc := P.junction_contract w G j hj
  intro goal l r d
  by_cases he : i = j
  · subst i
    exact incoming_line_turn_sparse w hw _ _ hc.incoming_good hc.perpendicular hc.incoming_last
      hc.incoming_direction hc.incoming_finish rfl rfl goal l r d
  by_cases he' : i = j+1
  · subst i
    exact outgoing_line_turn_sparse w hw _ _ hc.outgoing_good hc.perpendicular hc.outgoing_first
      hc.outgoing_direction hc.outgoing_start rfl rfl goal l r d
  by_cases hij : i < j
  · obtain ⟨u,hu,ha⟩ := P.line_actor_at w hw G i hi goal l
    have hb := P.turn_actor_at w hw G j hj goal r
    rw [P.join_eq w G j hj.1] at hb
    exact P.marks_not_adjacent w G i (j+1) hi hj.1 (by omega) 1 2
      (by unfold FiniteGeometry.origin; omega) hu (P.start_contains w G (j+1) hj.1) ha hb d
  · obtain ⟨v,hv,hb⟩ := P.line_actor_at w hw G i hi goal l
    have ha := P.turn_actor_at w hw G j hj goal r
    intro hadj
    exact P.marks_not_adjacent w G j i (by omega) hi (by omega) 2 1
      (by unfold FiniteGeometry.origin; omega) (P.finish_contains w G j (by omega)) hv ha hb d.opposite
      (travels_one_reverse hadj)

private theorem turns_actor_sparse (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : P.hasTurn i) (hj : P.hasTurn j) (hij : i < j) :
    ActorsSparse w hw (.turn (P.turn i)) (.turn (P.turn j)) := by
  intro goal l r d
  have ha := P.turn_actor_at w hw G i hi goal l
  have hb := P.turn_actor_at w hw G j hj goal r
  rw [P.join_eq w G j hj.1] at hb
  exact P.marks_not_adjacent w G i (j+1) (by have := hi.1; omega) hj.1 (by omega) 2 2
    (by unfold FiniteGeometry.origin; omega) (P.finish_contains w G i (by have := hi.1; omega))
    (P.start_contains w G (j+1) hj.1) ha hb d

private theorem block_sparse (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : i < P.segments.length) : (P.block i).Pairwise (ActorsSparse w hw) := by
  by_cases ht : P.hasTurn i
  · simp only [block,ht,↓reduceIte,List.singleton_append]
    apply List.pairwise_cons.mpr
    refine ⟨?_,by simp⟩
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact P.line_turn_sparse w hw G i i hi ht
  · simp only [block,ht,↓reduceIte,List.append_nil,List.pairwise_singleton]

private theorem blocks_sparse (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : j < P.segments.length) (hij : i < j)
    (c : PrimitiveCode) (hc : c ∈ P.block i) (e : PrimitiveCode) (he : e ∈ P.block j) :
    ActorsSparse w hw c e := by
  rcases (P.mem_block i c).mp hc with rfl | ⟨hti,rfl⟩ <;>
    rcases (P.mem_block j e).mp he with rfl | ⟨htj,rfl⟩
  · exact P.lines_actor_sparse w hw G i j hi hj hij
  · exact P.line_turn_sparse w hw G i j hi htj
  · exact (P.line_turn_sparse w hw G j i hj hti).symm
  · exact P.turns_actor_sparse w hw G i j hti htj hij

theorem codes_sparse (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w) :
    P.codes.Pairwise (ActorsSparse w hw) := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun i hi => P.block_sparse w hw G i (List.mem_range.mp hi),?_⟩
  apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range
  intro i j hi hj hij
  exact P.blocks_sparse w hw G i j (List.mem_range.mp hi) (List.mem_range.mp hj) hij

end PathSpec
end PushPuzzle.PushS.FiniteRouting
