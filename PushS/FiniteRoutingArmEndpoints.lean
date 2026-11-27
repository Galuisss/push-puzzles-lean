/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingSharedSlots

/-! Literal first and final shared slots of the complete actual gate arms. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction FiniteGeometry

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem route_first_direction (w : ℕ) (kind : Bool) (q : Key) :
    segmentDirection (segmentAt (route w kind q) 0) = PortAnnulus.innerDirection q.2.2 := by
  have hfirst : segmentAt (route w kind q) 0 =
      ⟨corePort w kind q.2.2,(adapterVertices w kind q.2.2).getD 1 (0,0)⟩ := by
    rcases q with ⟨pattern,rotation,role⟩
    fin_cases role <;> simp [segmentAt,route,adapter,adapterVertices]
  rw [hfirst]
  exact segmentDirection_of_runs _ _ _ (adapter_endpoints w kind q.2.2).2.2.1

private theorem armRoute_first_eq (w : ℕ) (g : GateTileState) (role : Fin 3) :
    segmentAt (armRoute w g role) 0 = segmentAt (route w g.core.isAND (g.pattern,g.rotation,role)) 0 := by
  have hi : 0 < (route w g.core.isAND (g.pattern,g.rotation,role)).length := by rw [route_length]; omega
  have ha : 0 < (armRoute w g role).length := by rwa [armRoute_length]
  have hn : 0+1 ≠ (route w g.core.isAND (g.pattern,g.rotation,role)).length := by rw [route_length]; omega
  unfold segmentAt
  rw [List.getD_eq_getElem (armRoute w g role) _ ha,
    List.getD_eq_getElem (route w g.core.isAND (g.pattern,g.rotation,role)) _ hi]
  simp only [armRoute,List.getElem_mapIdx,hn,↓reduceIte]

theorem armSpec_first_start (w : ℕ) (g : GateTileState) (role : Fin 3) :
    ((armSpec w g role).line 0).segment.start = corePort w g.core.isAND role := by
  change (trimmedSegment (armRoute w g role) 0).start = _
  simp only [trimmedSegment,trimmed,startTrim,ite_true,advance_zero,armRoute_first_eq]
  simpa only [segmentAt,List.headD_eq_getD] using route_first_start w g.core.isAND (g.pattern,g.rotation,role)

theorem armSpec_first_direction (w : ℕ) (g : GateTileState) (role : Fin 3) :
    segmentDirection ((armSpec w g role).line 0).segment = PortAnnulus.innerDirection role := by
  rw [show segmentDirection ((armSpec w g role).line 0).segment =
      segmentDirection (segmentAt (armRoute w g role) 0) from
        trimmedSegment_direction w _ (armRoute_good w g role) 0 (by rw [armRoute_length,route_length]; omega),
    armRoute_first_eq]
  exact route_first_direction w g.core.isAND (g.pattern,g.rotation,role)

theorem armSpec_first_slot (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3) (phase : Bool) :
    ((armSpec w g role).line 0).firstWorld w hw phase =
      Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) phase.toNat := by
  rw [LineCode.firstWorld_eq w hw _ ((armSpec w g role).line_good w (armSpec_geometry w g role) 0
    (by change 0 < (armRoute w g role).length; rw [armRoute_length,route_length]; omega)),
    armSpec_first_direction,armSpec_first_start]

theorem and_arm_first_shared (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (kind : g.core.isAND = true)
    (role : Fin 3) (a b c : Bool) :
    ((armSpec w g role).line 0).firstWorld w hw (portInflow a b c role) =
      coreWorld w (andCell w a b c (andPortLabel w role)) := by
  rw [armSpec_first_slot,kind,andPort_world]

theorem or_arm_first_shared (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (kind : g.core.isAND = false)
    (role : Fin 3) (a b c : Bool) :
    ((armSpec w g role).line 0).firstWorld w hw (portInflow a b c role) =
      coreWorld w (orCell w a b c (orPortLabel w role)) := by
  rw [armSpec_first_slot,kind,orPort_world]

theorem segmentAt_last (segments : List Segment) :
    segmentAt segments (segments.length-1) = segments.getLastD ⟨(0,0),(0,0)⟩ := by
  induction segments using List.reverseRecOn with
  | nil => rfl
  | append_singleton segments s ih =>
    simp only [segmentAt,List.length_append,List.length_singleton,Nat.add_sub_cancel]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [Nat.sub_self,List.getD_cons_zero,List.getLastD_concat]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem source_last_direction : ∀ q : Key,
    segmentDirection ((PortAnnulus.curve q).getLastD ⟨(0,0),(0,0)⟩) = PortAnnulus.outerDirection q := by
  decide +kernel

private theorem curve_last_direction (w : ℕ) (q : Key) :
    segmentDirection ((curve w q).getLastD ⟨(0,0),(0,0)⟩) = PortAnnulus.outerDirection q := by
  have hz : scaleSegment (spacing w) ⟨(0,0),(0,0)⟩ = ⟨(0,0),(0,0)⟩ := by simp [scaleSegment,scalePoint]
  have h := @List.getLastD_map _ _ (scaleSegment (spacing w)) (PortAnnulus.curve q) ⟨(0,0),(0,0)⟩
  have he : (curve w q).getLastD ⟨(0,0),(0,0)⟩ =
      scaleSegment (spacing w) ((PortAnnulus.curve q).getLastD ⟨(0,0),(0,0)⟩) := by
    simpa only [curve,hz] using h
  rw [he,segmentDirection_scale _ (spacing_pos w),source_last_direction]

theorem route_last_direction (w : ℕ) (kind : Bool) (q : Key) :
    segmentDirection (segmentAt (route w kind q) ((route w kind q).length-1)) = PortAnnulus.outerDirection q := by
  rw [segmentAt_last]
  have hne := curve_nonempty w q
  cases he : (curve w q).getLast? with
  | none => simp_all
  | some s =>
    simpa only [route,List.getLastD_eq_getLast?,List.getLast?_append,he,Option.some_or,
      Option.getD_some] using curve_last_direction w q

private theorem direction_at_map (segments : List Segment) (i : ℕ) :
    segmentDirection (segmentAt segments i) = (segments.map segmentDirection).getD i .north := by
  simpa only [segmentAt,show segmentDirection ⟨(0,0),(0,0)⟩ = .north by rfl] using
    (List.getD_map (l := segments) (d := ⟨(0,0),(0,0)⟩) (n := i) segmentDirection).symm

private theorem armRoute_direction_at (w : ℕ) (g : GateTileState) (role : Fin 3) (i : ℕ) :
    segmentDirection (segmentAt (armRoute w g role) i) =
      segmentDirection (segmentAt (route w g.core.isAND (g.pattern,g.rotation,role)) i) := by
  rw [direction_at_map,armRoute_directions,←direction_at_map]

private theorem armRoute_last_eq (w : ℕ) (g : GateTileState) (role : Fin 3) :
    segmentAt (armRoute w g role) ((armRoute w g role).length-1) =
      let s := segmentAt (route w g.core.isAND (g.pattern,g.rotation,role))
        ((route w g.core.isAND (g.pattern,g.rotation,role)).length-1)
      ⟨s.start,advance (segmentDirection s).opposite s.finish (g.incoming.get role).toNat⟩ := by
  rw [armRoute_length]
  have hi : (route w g.core.isAND (g.pattern,g.rotation,role)).length-1 <
      (route w g.core.isAND (g.pattern,g.rotation,role)).length := by rw [route_length]; omega
  have ha : (route w g.core.isAND (g.pattern,g.rotation,role)).length-1 < (armRoute w g role).length := by
    rwa [armRoute_length]
  have hn : (route w g.core.isAND (g.pattern,g.rotation,role)).length-1+1 =
      (route w g.core.isAND (g.pattern,g.rotation,role)).length := by omega
  dsimp only
  unfold segmentAt
  rw [List.getD_eq_getElem (armRoute w g role) _ ha,
    List.getD_eq_getElem (route w g.core.isAND (g.pattern,g.rotation,role)) _ hi]
  simp only [armRoute,List.getElem_mapIdx,hn,ite_true]

theorem outerPoint_eq_boundary (w : ℕ) (d : Direction) :
    scalePoint (spacing w) (PortAnnulus.outerPoint d) = boundaryPoint w d := by
  cases d <;> simp [scalePoint,PortAnnulus.outerPoint,boundaryPoint,tileStride,Nat.mul_comm]

theorem armSpec_last_finish (w : ℕ) (g : GateTileState) (role : Fin 3) :
    ((armSpec w g role).line ((armRoute w g role).length-1)).segment.finish =
      advance (PortAnnulus.outerDirection (g.pattern,g.rotation,role)).opposite
        (boundaryPoint w (PortAnnulus.outerDirection (g.pattern,g.rotation,role))) (g.incoming.get role).toNat := by
  have hi : (armRoute w g role).length-1+1 = (armRoute w g role).length := by rw [armRoute_length,route_length]; omega
  change (trimmedSegment (armRoute w g role) ((armRoute w g role).length-1)).finish = _
  simp only [trimmedSegment,trimmed,finishTrim,hi,ite_true,advance_zero,armRoute_last_eq]
  rw [route_last_direction,segmentAt_last,route_last_finish,outerPoint_eq_boundary]

theorem armSpec_last_direction (w : ℕ) (g : GateTileState) (role : Fin 3) :
    segmentDirection ((armSpec w g role).line ((armRoute w g role).length-1)).segment =
      PortAnnulus.outerDirection (g.pattern,g.rotation,role) := by
  change segmentDirection (trimmedSegment (armRoute w g role) _) = _
  rw [trimmedSegment_direction w _ (armRoute_good w g role) _
    (by rw [armRoute_length,route_length]; omega),armRoute_direction_at,armRoute_length,route_last_direction]

theorem armSpec_last_slot (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3) (phase : Bool) :
    ((armSpec w g role).line ((armRoute w g role).length-1)).lastWorld w hw phase =
      boundarySlot w (PortAnnulus.outerDirection (g.pattern,g.rotation,role)) (g.incoming.get role) phase := by
  rw [LineCode.lastWorld_eq w hw _ ((armSpec w g role).line_good w (armSpec_geometry w g role) _
    (by change (armRoute w g role).length-1 < (armRoute w g role).length; rw [armRoute_length,route_length]; omega)),
    armSpec_last_direction,armSpec_last_finish]
  cases g.incoming.get role <;> simp only [boundarySlot,Bool.toNat_false,Bool.toNat_true,
    Bool.false_eq_true,↓reduceIte,advance_zero]

end PushPuzzle.PushS.FiniteRouting
