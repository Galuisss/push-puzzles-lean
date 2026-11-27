/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingGateGeometry
public import PushS.FiniteRoutingWireGeometry

/-! Only terminal straight pieces reach an actual source macrocell's narrow overlap collars. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

def RouteInterior (w : ℕ) (p : ℕ × ℕ) : Prop :=
  3*spacing w ≤ p.1 ∧ p.1 ≤ 47*spacing w ∧ 3*spacing w ≤ p.2 ∧ p.2 ≤ 47*spacing w

def TileInterior (w : ℕ) (p : ℕ × ℕ) : Prop :=
  2*padding w < p.1 ∧ p.1 < tileStride w ∧ 2*padding w < p.2 ∧ p.2 < tileStride w

def InCollar (w : ℕ) (d : Direction) (p : ℕ × ℕ) : Prop :=
  match d with
  | .north => p.2 ≤ 2*padding w
  | .east => tileStride w ≤ p.1
  | .south => tileStride w ≤ p.2
  | .west => p.1 ≤ 2*padding w

theorem interior_not_collar (w : ℕ) (d : Direction) {p : ℕ × ℕ} (hp : TileInterior w p) : ¬InCollar w d p := by
  cases d <;> dsimp [TileInterior,InCollar] at * <;> omega

theorem nearby_interior (w : ℕ) (m : ℕ) (hm : m ≤ padding w) {p a : ℕ × ℕ}
    (hp : RouteInterior w p) (ha : Nearby m a (padding w+p.1,padding w+p.2)) : TileInterior w a := by
  unfold RouteInterior TileInterior Nearby tileStride spacing padding at *
  omega

set_option maxRecDepth 65536 in
private theorem adapter_interior (w : ℕ) (kind : Bool) (role : Fin 3) {p : ℕ × ℕ}
    (hp : ∃ s ∈ adapter w kind role, s.Contains p) : RouteInterior w p := by
  obtain ⟨s,hs,hp⟩ := hp
  have hb := Segment.coordinate_bounds hp
  clear hp
  cases kind <;> fin_cases role <;> simp [adapter,adapterVertices,corePort,spacing] at hs <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> dsimp only at hb <;>
    unfold RouteInterior spacing <;> omega

private def SourceInterior (s : Segment) : Prop :=
  3 ≤ s.start.1 ∧ s.start.1 ≤ 47 ∧ 3 ≤ s.start.2 ∧ s.start.2 ≤ 47 ∧
    3 ≤ s.finish.1 ∧ s.finish.1 ≤ 47 ∧ 3 ≤ s.finish.2 ∧ s.finish.2 ≤ 47

private instance (s : Segment) : Decidable (SourceInterior s) := by unfold SourceInterior; infer_instance

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem source_nonlast_interior : ∀ q : Key, ∀ i : Fin (PortAnnulus.curve q).length,
    i.val+1 < (PortAnnulus.curve q).length →
      SourceInterior ((PortAnnulus.curve q).getD i.val ⟨(0,0),(0,0)⟩) := by decide +kernel

private theorem curve_nonlast_interior (w : ℕ) (q : Key) (i : ℕ) (hi : i+1 < (curve w q).length)
    {p : ℕ × ℕ} (hp : (segmentAt (curve w q) i).Contains p) : RouteInterior w p := by
  have hi' : i < (PortAnnulus.curve q).length := by simp only [curve_length] at hi; omega
  have hn' : i+1 < (PortAnnulus.curve q).length := by simpa only [curve_length] using hi
  have hs := source_nonlast_interior q ⟨i,hi'⟩ hn'
  have hz : scaleSegment (spacing w) ⟨(0,0),(0,0)⟩ = ⟨(0,0),(0,0)⟩ := by simp [scaleSegment,scalePoint]
  have hget := List.getD_map (l := PortAnnulus.curve q) (d := ⟨(0,0),(0,0)⟩) (n := i) (scaleSegment (spacing w))
  have he : segmentAt (curve w q) i = scaleSegment (spacing w) (segmentAt (PortAnnulus.curve q) i) := by
    simpa only [segmentAt,curve,hz] using hget
  rw [he] at hp
  have hb := Segment.coordinate_bounds hp
  unfold SourceInterior at hs
  dsimp [scaleSegment,scalePoint] at hb
  have hx0 := Nat.mul_le_mul_left (spacing w) hs.1
  have hx1 := Nat.mul_le_mul_left (spacing w) hs.2.1
  have hy0 := Nat.mul_le_mul_left (spacing w) hs.2.2.1
  have hy1 := Nat.mul_le_mul_left (spacing w) hs.2.2.2.1
  have hx2 := Nat.mul_le_mul_left (spacing w) hs.2.2.2.2.1
  have hx3 := Nat.mul_le_mul_left (spacing w) hs.2.2.2.2.2.1
  have hy2 := Nat.mul_le_mul_left (spacing w) hs.2.2.2.2.2.2.1
  have hy3 := Nat.mul_le_mul_left (spacing w) hs.2.2.2.2.2.2.2
  unfold RouteInterior
  simp only [segmentAt] at *
  omega

private theorem route_nonlast_interior (w : ℕ) (kind : Bool) (q : Key) (i : ℕ)
    (hi : i+1 < (route w kind q).length) {p : ℕ × ℕ}
    (hp : (segmentAt (route w kind q) i).Contains p) : RouteInterior w p := by
  simp only [route_length] at hi
  by_cases hia : i < 5
  · change ((adapter w kind q.2.2 ++ curve w q).getD i ⟨(0,0),(0,0)⟩).Contains p at hp
    rw [List.getD_append _ _ _ _ (by simpa only [adapter_length] using hia)] at hp
    apply adapter_interior w kind q.2.2
    refine ⟨_,?_,hp⟩
    rw [List.getD_eq_getElem _ _ (by simpa only [adapter_length] using hia)]
    exact List.getElem_mem _
  · change ((adapter w kind q.2.2 ++ curve w q).getD i ⟨(0,0),(0,0)⟩).Contains p at hp
    rw [List.getD_append_right _ _ _ _ (by simpa only [adapter_length] using (show 5 ≤ i by omega)),adapter_length] at hp
    exact curve_nonlast_interior w q (i-5) (by omega) hp

theorem armRoute_nonlast_interior (w : ℕ) (g : GateTileState) (role : Fin 3) (i : ℕ)
    (hi : i+1 < (armRoute w g role).length) {p : ℕ × ℕ}
    (hp : (segmentAt (armRoute w g role) i).Contains p) : RouteInterior w p := by
  have hi' : i < (armRoute w g role).length := by omega
  have hp' : ((armRoute w g role)[i]).Contains p := by simpa only [segmentAt,List.getD_eq_getElem _ _ hi'] using hp
  have hraw := armRoute_contains_getElem w g role i hi' hp'
  have hi'' : i < (route w g.core.isAND (g.pattern,g.rotation,role)).length := by simpa only [armRoute_length] using hi'
  apply route_nonlast_interior w g.core.isAND (g.pattern,g.rotation,role) i (by simpa only [←armRoute_length] using hi)
  simpa only [segmentAt,List.getD_eq_getElem _ _ hi''] using hraw

theorem core_window_interior (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (p : Cell ((PrimitiveCode.core g).instanceOf w hw).width ((PrimitiveCode.core g).instanceOf w hw).height) :
    TileInterior w ((PrimitiveCode.core g).world w hw p) := by
  rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
  cases kind <;> have hx := p.1.isLt <;> have hy := p.2.isLt
  all_goals
    change p.1.val < FiniteGeometry.side w at hx
    change p.2.val < FiniteGeometry.side w at hy
    dsimp [TileInterior,PrimitiveCode.world,PrimitiveCode.offsetX,PrimitiveCode.offsetY]
    unfold FiniteGeometry.side coreOffset tileStride spacing padding at *
    omega

theorem arm_nonlast_actor_interior (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3)
    (i : ℕ) (hi : i+1 < (armRoute w g role).length) (goal : Bool)
    (l : (PrimitiveCode.line ((armSpec w g role).line i)).Labels w) :
    TileInterior w ((PrimitiveCode.line ((armSpec w g role).line i)).actor w hw goal l) := by
  obtain ⟨u,hu,ha⟩ := (armSpec w g role).line_actor_at w hw (armSpec_geometry w g role) i (by exact Nat.lt_of_succ_lt hi) goal l
  exact nearby_interior w 1 (by unfold padding; omega) (armRoute_nonlast_interior w g role i hi hu) ha

theorem arm_nonlast_wall_interior (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3)
    (i : ℕ) (hi : i+1 < (armRoute w g role).length)
    (p : Cell ((PrimitiveCode.line ((armSpec w g role).line i)).instanceOf w hw).width
      ((PrimitiveCode.line ((armSpec w g role).line i)).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line ((armSpec w g role).line i)).instanceOf w hw).board.walls) :
    TileInterior w ((PrimitiveCode.line ((armSpec w g role).line i)).world w hw p) := by
  obtain ⟨u,hu,ha⟩ := (armSpec w g role).line_wall_at w hw (armSpec_geometry w g role) i (by exact Nat.lt_of_succ_lt hi) p hp
  exact nearby_interior w (w+1) (by unfold padding; omega) (armRoute_nonlast_interior w g role i hi hu) ha

theorem arm_turn_window_interior (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3)
    (i : ℕ) (hi : (armSpec w g role).hasTurn i) (p : Cell (FiniteTools.side w) (FiniteTools.side w)) :
    TileInterior w ((PrimitiveCode.turn ((armSpec w g role).turn i)).world w hw p) := by
  have hp := (armSpec w g role).turn_wall_at w hw i p
  have hu := (armSpec w g role).finish_contains w (armSpec_geometry w g role) i (by have h := hi.1; omega)
  exact nearby_interior w (FiniteTools.radius w) (by unfold FiniteTools.radius padding; omega)
    (armRoute_nonlast_interior w g role i hi.1 hu) hp

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem source_last_start_interior : ∀ q : Key,
    let s := (PortAnnulus.curve q).getLastD ⟨(0,0),(0,0)⟩
    3 ≤ s.start.1 ∧ s.start.1 ≤ 47 ∧ 3 ≤ s.start.2 ∧ s.start.2 ≤ 47 := by decide +kernel

private theorem route_last_start_interior (w : ℕ) (kind : Bool) (q : Key) :
    RouteInterior w (segmentAt (route w kind q) ((route w kind q).length-1)).start := by
  rw [segmentAt_last]
  have he : (route w kind q).getLastD ⟨(0,0),(0,0)⟩ = (curve w q).getLastD ⟨(0,0),(0,0)⟩ := by
    have hne := curve_nonempty w q
    cases h : (curve w q).getLast? with
    | none => simp_all
    | some s => simp only [route,List.getLastD_eq_getLast?,List.getLast?_append,h,Option.some_or,Option.getD_some]
  rw [he]
  have hz : scaleSegment (spacing w) ⟨(0,0),(0,0)⟩ = ⟨(0,0),(0,0)⟩ := by simp [scaleSegment,scalePoint]
  have hm := @List.getLastD_map _ _ (scaleSegment (spacing w)) (PortAnnulus.curve q) ⟨(0,0),(0,0)⟩
  have hm' : (curve w q).getLastD ⟨(0,0),(0,0)⟩ =
      scaleSegment (spacing w) ((PortAnnulus.curve q).getLastD ⟨(0,0),(0,0)⟩) := by
    simpa only [curve,hz] using hm
  rw [hm']
  have hs := source_last_start_interior q
  have hx0 := Nat.mul_le_mul_left (spacing w) hs.1
  have hx1 := Nat.mul_le_mul_left (spacing w) hs.2.1
  have hy0 := Nat.mul_le_mul_left (spacing w) hs.2.2.1
  have hy1 := Nat.mul_le_mul_left (spacing w) hs.2.2.2
  dsimp [RouteInterior,scaleSegment,scalePoint]
  omega

private theorem terminal_point_collar_face (w : ℕ) (d face : Direction) (start : ℕ × ℕ)
    (length m : ℕ)
    (hs : RouteInterior w start) (ht : Travels d start (boundaryPoint w d) length)
    (hm : m ≤ padding w) {u a : ℕ × ℕ}
    (hu : (⟨start,boundaryPoint w d⟩ : Segment).Contains u)
    (ha : Nearby m a (padding w+u.1,padding w+u.2)) (hf : InCollar w face a) : d = face := by
  have hb := Segment.coordinate_bounds hu
  cases d <;> cases face <;> first
    | rfl
    | (dsimp [Travels,boundaryPoint,RouteInterior,InCollar,Nearby] at *
       simp only [tileStride,spacing,padding] at *
       omega)

theorem arm_last_collar_face (w : ℕ) (g : GateTileState) (role : Fin 3) (face : Direction) (m : ℕ)
    (hm : m ≤ padding w) {u a : ℕ × ℕ}
    (hu : (segmentAt (armRoute w g role) ((armRoute w g role).length-1)).Contains u)
    (ha : Nearby m a (padding w+u.1,padding w+u.2)) (hf : InCollar w face a) :
    PortAnnulus.outerDirection (g.pattern,g.rotation,role) = face := by
  have hi : (armRoute w g role).length-1 < (armRoute w g role).length := by rw [armRoute_length,route_length]; omega
  have hu' : ((armRoute w g role)[(armRoute w g role).length-1]).Contains u := by
    simpa only [segmentAt,List.getD_eq_getElem _ _ hi] using hu
  have hraw := armRoute_contains_getElem w g role _ hi hu'
  have hiraw : (armRoute w g role).length-1 < (route w g.core.isAND (g.pattern,g.rotation,role)).length := by
    simpa only [armRoute_length] using hi
  have hu'' : (segmentAt (route w g.core.isAND (g.pattern,g.rotation,role))
      ((route w g.core.isAND (g.pattern,g.rotation,role)).length-1)).Contains u := by
    have hi'' : (route w g.core.isAND (g.pattern,g.rotation,role)).length-1 <
        (route w g.core.isAND (g.pattern,g.rotation,role)).length := by simpa only [armRoute_length] using hiraw
    simpa only [segmentAt,armRoute_length,List.getD_eq_getElem _ _ hi''] using hraw
  let s := segmentAt (route w g.core.isAND (g.pattern,g.rotation,role))
    ((route w g.core.isAND (g.pattern,g.rotation,role)).length-1)
  have hs := route_segment_good w g.core.isAND (g.pattern,g.rotation,role) (s := s)
    (by dsimp [s,segmentAt]; rw [List.getD_eq_getElem _ _ (by rw [route_length]; omega)]; exact List.getElem_mem _)
  have htravel := segment_travels s hs.1
  have hd : segmentDirection s = PortAnnulus.outerDirection (g.pattern,g.rotation,role) := route_last_direction _ _ _
  have hend : s.finish = boundaryPoint w (PortAnnulus.outerDirection (g.pattern,g.rotation,role)) := by
    dsimp [s]
    rw [segmentAt_last,route_last_finish,outerPoint_eq_boundary]
  rw [hd,hend] at htravel
  exact terminal_point_collar_face w _ face s.start (segmentLength s) m
    (route_last_start_interior w g.core.isAND (g.pattern,g.rotation,role)) htravel hm
    (by simpa only [←hend] using hu'') ha hf

end PushPuzzle.PushS.FiniteRouting
