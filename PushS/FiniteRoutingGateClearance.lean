/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingArmClearance
public import PushS.FiniteRoutingArmEndpoints

/-! The literal core inventory and all actual routed arm primitives have disjoint actors and clear floor. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

def coreSignals (g : GateTileState) (goal : Bool) : Gadgets.Gates.Signals :=
  if goal then g.core.target else g.core.initial

theorem core_ray_actor_separated (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3)
    (goal : Bool) (n : ℕ)
    (hn : (portInflow (coreSignals g goal).left (coreSignals g goal).upper
      (coreSignals g goal).right role).toNat+2 ≤ n) (l : (PrimitiveCode.core g).Labels w) :
    ¬Nearby 1 (Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) n)
      ((PrimitiveCode.core g).actor w hw goal l) := by
  rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
  cases kind <;> cases goal
  · exact orRay_boxes_separated w hw initial.left initial.upper initial.right role n hn l
  · exact orRay_boxes_separated w hw target.left target.upper target.right role n hn l
  · exact andRay_boxes_separated w hw initial.left initial.upper initial.right role n hn l
  · exact andRay_boxes_separated w hw target.left target.upper target.right role n hn l

theorem core_actor_outward_lane (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3)
    (goal : Bool) (l : (PrimitiveCode.core g).Labels w)
    (h : Outward (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) 0)
      ((PrimitiveCode.core g).actor w hw goal l)) :
    SameLane (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) 0)
      ((PrimitiveCode.core g).actor w hw goal l) := by
  rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
  cases kind <;> cases goal
  · exact orActor_outward_lane w hw initial.left initial.upper initial.right role l h
  · exact orActor_outward_lane w hw target.left target.upper target.right role l h
  · exact andActor_outward_lane w hw initial.left initial.upper initial.right role l h
  · exact andActor_outward_lane w hw target.left target.upper target.right role l h

theorem core_wall_ne_ray (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3) (n : ℕ)
    (p : Cell ((PrimitiveCode.core g).instanceOf w hw).width ((PrimitiveCode.core g).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.core g).instanceOf w hw).board.walls) :
    (PrimitiveCode.core g).world w hw p ≠
      Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) n := by
  rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
  cases kind
  · exact orRay_not_wall w hw role n p hp
  · exact andRay_not_wall w hw role n p hp

theorem core_tail_ne (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3) (margin : ℕ)
    (hm : margin ≤ FiniteGeometry.origin w) {u a : ℕ × ℕ}
    (hu : ∃ s ∈ (armRoute w g role).tail, s.Contains u)
    (ha : Nearby margin a (padding w+u.1,padding w+u.2))
    (p : Cell ((PrimitiveCode.core g).instanceOf w hw).width ((PrimitiveCode.core g).instanceOf w hw).height) :
    a ≠ (PrimitiveCode.core g).world w hw p := by
  have hraw := armRoute_tail_trace_subset w g role hu
  rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
  cases kind
  · exact route_tail_near_core_disjoint w false (pattern,rotation,role) margin hm hraw ha p
  · exact route_tail_near_core_disjoint w true (pattern,rotation,role) margin hm hraw ha p

theorem first_line_actor_formula (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3)
    (goal : Bool) (r : (PrimitiveCode.line ((armSpec w g role).line 0)).Labels w) :
    (PrimitiveCode.line ((armSpec w g role).line 0)).actor w hw goal r =
      Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role)
        (Line.position w
          (Line.program w (segmentLength ((armSpec w g role).line 0).segment)
            (((armSpec w g role).line 0).above != ((armSpec w g role).line 0).desiredSide))
          (portInflow (coreSignals g goal).left (coreSignals g goal).upper (coreSignals g goal).right role) r.val) := by
  rw [line_actor w hw _ ((armSpec w g role).line_good w (armSpec_geometry w g role) 0
    (by change 0 < (armRoute w g role).length; rw [armRoute_length,route_length]; omega)),
    armSpec_first_direction,armSpec_first_start]
  cases goal <;> rfl

private theorem core_first_line_actor_apart (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (role : Fin 3) :
    ActorsApart w hw (.core g) (.line ((armSpec w g role).line 0)) := by
  intro goal l r
  let c := (armSpec w g role).line 0
  let phase := portInflow (coreSignals g goal).left (coreSignals g goal).upper (coreSignals g goal).right role
  have hfirst : ((armSpec w g role).line 0).first = false := rfl
  let r' : Line.OwnedLabel w
      (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) false c.last :=
    ⟨r.val,by simpa only [c,hfirst] using r.property⟩
  have hpos := Line.owned_position_after_first w (segmentLength c.segment) hw (c.above != c.desiredSide) phase c.last r'
  have hsep := core_ray_actor_separated w hw g role goal _ hpos l
  rw [first_line_actor_formula]
  intro he
  apply hsep
  rw [←he]
  unfold Nearby
  omega

private theorem first_line_core_wall_clear (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3) :
    ActorWallsClear w hw (.line ((armSpec w g role).line 0)) (.core g) := by
  intro goal l p hp
  rw [first_line_actor_formula]
  exact Ne.symm (core_wall_ne_ray w hw g role _ p hp)

private theorem core_first_line_wall_clear (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3) :
    ActorWallsClear w hw (.core g) (.line ((armSpec w g role).line 0)) := by
  intro goal l p hp
  obtain ⟨ho,_,hn⟩ := line_wall_envelope w hw _
    ((armSpec w g role).line_good w (armSpec_geometry w g role) 0
      (by change 0 < (armRoute w g role).length; rw [armRoute_length,route_length]; omega)) p hp
  rw [armSpec_first_direction,armSpec_first_start] at ho hn
  intro he
  rw [←he] at ho hn
  exact hn (core_actor_outward_lane w hw g role goal l ho)

theorem core_arm_actor_apart (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3)
    (c : PrimitiveCode) (hc : c ∈ (armSpec w g role).codes) : ActorsApart w hw (.core g) c := by
  let P := armSpec w g role
  have G : P.Geometry w := armSpec_geometry w g role
  change c ∈ P.codes at hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases (P.mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · by_cases hz : i = 0
    · subst i
      exact core_first_line_actor_apart w hw g role
    · intro goal l r
      obtain ⟨u,hu,ha⟩ := P.line_actor_at w hw G i hi' goal r
      exact Ne.symm (core_tail_ne w hw g role 1 (by unfold FiniteGeometry.origin; omega)
        ⟨_,P.segment_mem_tail i hi' (by omega),hu⟩ ha
        (if goal then (PrimitiveCode.matching w hw (.core g)).target l else
          (PrimitiveCode.matching w hw (.core g)).source l))
  · intro goal l r
    have ha := P.turn_actor_at w hw G i ht goal r
    rw [P.join_eq w G i ht.1] at ha
    exact Ne.symm (core_tail_ne w hw g role 2 (by unfold FiniteGeometry.origin; omega)
      ⟨_,P.segment_mem_tail (i+1) ht.1 (by omega),P.start_contains w G (i+1) ht.1⟩ ha
      (if goal then (PrimitiveCode.matching w hw (.core g)).target l else
        (PrimitiveCode.matching w hw (.core g)).source l))

theorem core_arm_wall_clear (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3)
    (c : PrimitiveCode) (hc : c ∈ (armSpec w g role).codes) : ActorWallsClear w hw (.core g) c := by
  let P := armSpec w g role
  have G : P.Geometry w := armSpec_geometry w g role
  change c ∈ P.codes at hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases (P.mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · by_cases hz : i = 0
    · subst i
      exact core_first_line_wall_clear w hw g role
    · intro goal l p hp
      obtain ⟨u,hu,ha⟩ := P.line_wall_at w hw G i hi' p hp
      exact Ne.symm (core_tail_ne w hw g role (w+1) (by unfold FiniteGeometry.origin; omega)
        ⟨_,P.segment_mem_tail i hi' (by omega),hu⟩ ha
        (if goal then (PrimitiveCode.matching w hw (.core g)).target l else
          (PrimitiveCode.matching w hw (.core g)).source l))
  · intro goal l p hp
    have ha := P.turn_wall_at w hw i p
    rw [P.join_eq w G i ht.1] at ha
    exact Ne.symm (core_tail_ne w hw g role (FiniteTools.radius w)
      (by unfold FiniteGeometry.origin FiniteTools.radius; omega)
      ⟨_,P.segment_mem_tail (i+1) ht.1 (by omega),P.start_contains w G (i+1) ht.1⟩ ha
      (if goal then (PrimitiveCode.matching w hw (.core g)).target l else
        (PrimitiveCode.matching w hw (.core g)).source l))

theorem arm_core_wall_clear (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3)
    (c : PrimitiveCode) (hc : c ∈ (armSpec w g role).codes) : ActorWallsClear w hw c (.core g) := by
  let P := armSpec w g role
  have G : P.Geometry w := armSpec_geometry w g role
  change c ∈ P.codes at hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases (P.mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · by_cases hz : i = 0
    · subst i
      exact first_line_core_wall_clear w hw g role
    · intro goal l p hp
      obtain ⟨u,hu,ha⟩ := P.line_actor_at w hw G i hi' goal l
      exact core_tail_ne w hw g role 1 (by unfold FiniteGeometry.origin; omega)
        ⟨_,P.segment_mem_tail i hi' (by omega),hu⟩ ha p
  · intro goal l p hp
    have ha := P.turn_actor_at w hw G i ht goal l
    rw [P.join_eq w G i ht.1] at ha
    exact core_tail_ne w hw g role 2 (by unfold FiniteGeometry.origin; omega)
      ⟨_,P.segment_mem_tail (i+1) ht.1 (by omega),P.start_contains w G (i+1) ht.1⟩ ha p

end PushPuzzle.PushS.FiniteRouting
