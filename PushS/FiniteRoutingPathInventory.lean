/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPathClearance

/-! Complete normal inventories of the literal multi-segment route instruction lists. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteTools.turnWalls

def ActorsApart (w : ℕ) (hw : 2 ≤ w) (c d : PrimitiveCode) : Prop :=
  ∀ (goal : Bool) (l : c.Labels w) (r : d.Labels w), c.actor w hw goal l ≠ d.actor w hw goal r

def ActorWallsClear (w : ℕ) (hw : 2 ≤ w) (c d : PrimitiveCode) : Prop :=
  ∀ (goal : Bool) (l : c.Labels w)
    (p : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height),
    p ∈ (d.instanceOf w hw).board.walls → c.actor w hw goal l ≠ d.world w hw p

namespace PathSpec

theorem mem_block (P : PathSpec) (i : ℕ) (c : PrimitiveCode) :
    c ∈ P.block i ↔ c = .line (P.line i) ∨ P.hasTurn i ∧ c = .turn (P.turn i) := by
  unfold block
  split_ifs <;> simp_all

private theorem block_pairwise (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : i < P.segments.length) : (P.block i).Pairwise (ActorsApart w hw) := by
  by_cases ht : P.hasTurn i
  · simp only [block,ht,↓reduceIte,List.singleton_append]
    apply List.pairwise_cons.mpr
    refine ⟨?_,by simp⟩
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact P.line_turn_actor_ne w hw G i i hi ht
  · simp only [block,ht,↓reduceIte,List.append_nil,List.pairwise_singleton]

private theorem blocks_actor_apart (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : j < P.segments.length) (hij : i < j)
    (c : PrimitiveCode) (hc : c ∈ P.block i) (d : PrimitiveCode) (hd : d ∈ P.block j) :
    ActorsApart w hw c d := by
  rcases (P.mem_block i c).mp hc with rfl | ⟨hti,rfl⟩ <;>
    rcases (P.mem_block j d).mp hd with rfl | ⟨htj,rfl⟩
  · exact P.lines_actor_ne w hw G i j hi hj hij
  · exact P.line_turn_actor_ne w hw G i j hi htj
  · intro goal l r
    exact Ne.symm (P.line_turn_actor_ne w hw G j i hj hti goal r l)
  · exact P.turns_actor_ne w hw G i j hti htj hij

theorem codes_pairwise (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w) :
    P.codes.Pairwise (ActorsApart w hw) := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun i hi => P.block_pairwise w hw G i (List.mem_range.mp hi),?_⟩
  apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range
  intro i j hi hj hij
  exact P.blocks_actor_apart w hw G i j (List.mem_range.mp hi) (List.mem_range.mp hj) hij

theorem codes_wall_clear (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (c : PrimitiveCode) (hc : c ∈ P.codes) (d : PrimitiveCode) (hd : d ∈ P.codes) :
    ActorWallsClear w hw c d := by
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨j,hj,hd⟩ := List.mem_flatMap.mp hd
  have hi' := List.mem_range.mp hi
  have hj' := List.mem_range.mp hj
  rcases (P.mem_block i c).mp hc with rfl | ⟨hti,rfl⟩ <;>
    rcases (P.mem_block j d).mp hd with rfl | ⟨htj,rfl⟩
  · exact P.lines_actor_wall_ne w hw G i j hi' hj'
  · exact P.line_turn_wall_ne w hw G i j hi' htj
  · exact P.turn_line_wall_ne w hw G j i hj' hti
  · exact P.turns_actor_wall_ne w hw G i j hti htj

end PathSpec

end PushPuzzle.PushS.FiniteRouting
