/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPathHulls
public import PushS.FiniteRoutingGateGeometry

/-! Full normal-travel intervals of distinct actual gate primitives are disjoint. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction FiniteGeometry

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem core_hull_ne_ray (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3) (n : ℕ)
    (hn : 2 ≤ n)
    (l : (PrimitiveCode.core g).Labels w) (a : ℕ × ℕ) (ha : ActorHull w hw (.core g) l a) :
    a ≠ Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) n := by
  rcases g with ⟨⟨kind,s,t⟩,incoming,pattern,rotation⟩
  have hsa := Bool.toNat_le s.left
  have hsb := Bool.toNat_le s.upper
  have hsc := Bool.toNat_le s.right
  have hta := Bool.toNat_le t.left
  have htb := Bool.toNat_le t.upper
  have htc := Bool.toNat_le t.right
  cases kind
  · have hs := orPoint_actor_bounds w hw s.left s.upper s.right l
    have ht := orPoint_actor_bounds w hw t.left t.upper t.right l
    change Hull (coreWorld w (orCell w s.left s.upper s.right l)) (coreWorld w (orCell w t.left t.upper t.right l)) a at ha
    intro he
    rw [he] at ha
    fin_cases role <;> dsimp [Hull,Line.along,PortAnnulus.innerDirection,corePort,coreWorld,orCell] at ha <;>
      simp only [origin,coreOffset,padding,spacing] at * <;> omega
  · have hs := andPoint_actor_bounds w hw s.left s.upper s.right l
    have ht := andPoint_actor_bounds w hw t.left t.upper t.right l
    change Hull (coreWorld w (andCell w s.left s.upper s.right l)) (coreWorld w (andCell w t.left t.upper t.right l)) a at ha
    intro he
    rw [he] at ha
    fin_cases role <;> dsimp [Hull,Line.along,PortAnnulus.innerDirection,corePort,coreWorld,andCell] at ha <;>
      simp only [origin,coreOffset,padding,spacing] at * <;> omega

private theorem core_arm_hulls_apart (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3)
    (c : PrimitiveCode) (hc : c ∈ (armSpec w g role).codes) : HullsApart w hw (.core g) c := by
  let P := armSpec w g role
  have G : P.Geometry w := armSpec_geometry w g role
  change c ∈ P.codes at hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases (P.mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · by_cases hz : i = 0
    · subst i
      intro l r a b ha hb
      obtain ⟨n,hn,_,_,he⟩ := line_hull_bounds w hw (P.line 0) (P.line_good w G 0 hi') rfl r b hb
      rw [armSpec_first_direction,armSpec_first_start] at he
      rw [he]
      exact core_hull_ne_ray w hw g role n hn l a ha
    · intro l r a b ha hb
      obtain ⟨p,hp⟩ := actor_hull_cell w hw (.core g) l a ha
      obtain ⟨u,hu,hb⟩ := P.line_hull_at w hw G i hi' r b hb
      rw [←hp]
      exact Ne.symm (core_tail_ne w hw g role 1 (by unfold origin; omega)
        ⟨_,P.segment_mem_tail i hi' (by omega),hu⟩ hb p)
  · intro l r a b ha hb
    obtain ⟨p,hp⟩ := actor_hull_cell w hw (.core g) l a ha
    have hb := P.turn_hull_at w hw G i ht r b hb
    rw [P.join_eq w G i ht.1] at hb
    rw [←hp]
    exact Ne.symm (core_tail_ne w hw g role 2 (by unfold origin; omega)
      ⟨_,P.segment_mem_tail (i+1) ht.1 (by omega),P.start_contains w G (i+1) ht.1⟩ hb p)

private theorem PathSpec.code_hull_trace (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (c : PrimitiveCode) (hc : c ∈ P.codes) (l : c.Labels w) (a : ℕ × ℕ) (ha : ActorHull w hw c l a) :
    ∃ u, (∃ s ∈ P.segments, s.Contains u) ∧ Nearby 2 a (padding w+u.1,padding w+u.2) := by
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases (P.mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · obtain ⟨u,hu,ha⟩ := P.line_hull_at w hw G i hi' l a ha
    exact ⟨u,⟨_,P.segment_mem i hi',hu⟩,nearby_of_le (by omega) ha⟩
  · exact ⟨_,⟨_,P.segment_mem i hi',P.finish_contains w G i hi'⟩,P.turn_hull_at w hw G i ht l a ha⟩

private theorem different_arms_hulls_apart (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (i j : Fin 3) (hij : i ≠ j) (c e : PrimitiveCode)
    (hc : c ∈ (armSpec w g i).codes) (he : e ∈ (armSpec w g j).codes) : HullsApart w hw c e := by
  intro l r a b ha hb
  obtain ⟨u,hu,ha⟩ := (armSpec w g i).code_hull_trace w hw (armSpec_geometry w g i) c hc l a ha
  obtain ⟨v,hv,hb⟩ := (armSpec w g j).code_hull_trace w hw (armSpec_geometry w g j) e he r b hb
  exact footprint_ne (w := w)
    (fun hn => armRoutes_separated_wide w g hij hu hv (nearby_of_le (by omega) hn)) ha hb

theorem gateCodes_hulls_pairwise (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) :
    (gateCodes w g).Pairwise (HullsApart w hw) := by
  rw [gateCodes_eq_specs,List.pairwise_cons]
  refine ⟨?_,?_⟩
  · intro c hc
    obtain ⟨role,_,hc⟩ := List.mem_flatMap.mp hc
    exact core_arm_hulls_apart w hw g role c hc
  · apply List.pairwise_flatMap.mpr
    refine ⟨fun role _ => (armSpec w g role).codes_hulls_pairwise w hw (armSpec_geometry w g role),?_⟩
    apply List.Pairwise.imp _ (List.nodup_iff_pairwise_ne.mp (List.nodup_finRange 3))
    intro i j hij c hc e he
    exact different_arms_hulls_apart w hw g i j hij c e hc he

end PushPuzzle.PushS.FiniteRouting
