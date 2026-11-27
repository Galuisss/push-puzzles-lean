/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingGateCollars

/-! Every actual ordinary wire collar has the common exposed port lane. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteTools.turnWalls

def CenteredLine (w : ℕ) (s : Segment) : Prop :=
  (s.start.2 = 25*spacing w ∧ s.finish.2 = 25*spacing w) ∨
    (s.start.1 = 25*spacing w ∧ s.finish.1 = 25*spacing w)

def wireSpec (w : ℕ) (q : Catalog.Bitmap.Args) : PathSpec :=
  ⟨wireRoute w q.1,false,false,true,q.2.1,q.2.2⟩

theorem wireSpec_geometry (w : ℕ) (q : Catalog.Bitmap.Args) : (wireSpec w q).Geometry w := by
  refine ⟨wireRoute_good w q.1,wireRoute_joined w q.1,wireRoute_directions_chain w q.1,?_⟩
  intro i j hij
  have hj := j.isLt
  have hlen : (wireRoute w q.1).length ≤ 2 := by rw [wireRoute_length]; split_ifs <;> omega
  change j.val < (wireRoute w q.1).length at hj
  omega

private theorem wire_segment_centered (w : ℕ) (kind : Catalog.Kind) (s : Segment)
    (hs : s ∈ wireRoute w kind) :
    CenteredLine w s := by
  cases kind <;> simp [wireRoute,wireVertices] at hs <;> rcases hs with rfl | rfl <;> simp [CenteredLine]

private theorem centered_trim (w : ℕ) (s : Segment) (hs : SegmentGood w s) (hc : CenteredLine w s)
    (front back : ℕ) : CenteredLine w (trimmed s front back) := by
  have ht := segment_travels s hs.1
  have hl := hs.2.1
  cases hd : segmentDirection s <;> dsimp [CenteredLine,trimmed] at * <;>
    simp only [hd] at * <;> dsimp [advance,Direction.opposite,Travels] at * <;> omega

theorem wire_line_centered (w : ℕ) (q : Catalog.Bitmap.Args) (i : ℕ)
    (hi : i < (wireRoute w q.1).length) : CenteredLine w ((wireSpec w q).line i).segment := by
  have hm : segmentAt (wireRoute w q.1) i ∈ wireRoute w q.1 := (wireSpec w q).segment_mem i hi
  exact centered_trim w _ (wireRoute_good w q.1 _ hm) (wire_segment_centered w q.1 _ hm) _ _

private theorem centered_actor_collar_lane (w : ℕ) (hw : 2 ≤ w) (c : LineCode)
    (hc : LineGood w c.segment)
    (hcenter : CenteredLine w c.segment) (goal : Bool) (l : (PrimitiveCode.line c).Labels w)
    (face : Direction) (hf : InCollar w face ((PrimitiveCode.line c).actor w hw goal l)) :
    SameLane face (Line.along w face (boundaryPoint w face) 0) ((PrimitiveCode.line c).actor w hw goal l) := by
  rw [line_actor w hw c hc goal l] at hf ⊢
  have ht := segment_travels c.segment hc.1
  have hl := hc.2.1
  cases hd : segmentDirection c.segment <;> cases face <;> simp only [hd] at hf ht ⊢ <;>
    dsimp [CenteredLine,SameLane,Line.along,InCollar,Travels,boundaryPoint] at * <;>
    simp only [tileStride,spacing,padding] at * <;> omega

private theorem centered_wall_collar_off_lane (w : ℕ) (hw : 2 ≤ w) (c : LineCode)
    (hc : LineGood w c.segment)
    (hcenter : CenteredLine w c.segment)
    (p : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) (face : Direction)
    (hf : InCollar w face ((PrimitiveCode.line c).world w hw p)) :
    ¬SameLane face (Line.along w face (boundaryPoint w face) 0) ((PrimitiveCode.line c).world w hw p) := by
  obtain ⟨_,_,hn⟩ := line_wall_envelope w hw c hc p hp
  obtain ⟨u,hu,ha⟩ := line_wall_footprint w hw c hc p hp
  have hb := Segment.coordinate_bounds hu
  have ht := segment_travels c.segment hc.1
  have hl := hc.2.1
  cases hd : segmentDirection c.segment <;> cases face <;> simp only [hd] at hn ht ⊢ <;>
    dsimp [CenteredLine,SameLane,Line.along,InCollar,Travels,boundaryPoint,Nearby] at * <;>
    simp only [tileStride,spacing,padding] at * <;> omega

private theorem wire_turn_corner (w : ℕ) (q : Catalog.Bitmap.Args) (i : ℕ) (hi :
    (wireSpec w q).hasTurn i) :
    ((wireSpec w q).turn i).corner = (25*spacing w,25*spacing w) := by
  have hil := hi.1
  change i+1 < (wireRoute w q.1).length at hil
  have hlen : (wireRoute w q.1).length ≤ 2 := by rw [wireRoute_length]; split_ifs <;> omega
  have hiz : i = 0 := by omega
  subst i
  rcases q with ⟨kind,initial,target⟩
  cases kind <;> simp [wireRoute,wireVertices] at hil <;> rfl

theorem wire_turn_window_interior (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args)
    (i : ℕ) (hi : (wireSpec w q).hasTurn i) (p : Cell (FiniteTools.side w) (FiniteTools.side w)) :
    TileInterior w ((PrimitiveCode.turn ((wireSpec w q).turn i)).world w hw p) := by
  have ha := turn_window_footprint w hw ((wireSpec w q).turn i) p
  rw [wire_turn_corner w q i hi] at ha
  exact nearby_interior w (FiniteTools.radius w) (by unfold FiniteTools.radius padding; omega)
    (by dsimp [RouteInterior]; omega) ha

theorem wire_actor_collar_lane (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) (c : PrimitiveCode)
    (hc : c ∈ wireCodes w q) (goal : Bool) (l : c.Labels w) (face : Direction)
    (hf : InCollar w face (c.actor w hw goal l)) :
    SameLane face (Line.along w face (boundaryPoint w face) 0) (c.actor w hw goal l) := by
  change c ∈ (wireSpec w q).codes at hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases ((wireSpec w q).mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · exact centered_actor_collar_lane w hw _ ((wireSpec w q).line_good w (wireSpec_geometry w q) i hi')
      (wire_line_centered w q i hi') goal l face hf
  · exact ((interior_not_collar w face (wire_turn_window_interior w hw q i ht
      (if goal then (PrimitiveCode.matching w hw (.turn ((wireSpec w q).turn i))).target l else
        (PrimitiveCode.matching w hw (.turn ((wireSpec w q).turn i))).source l))) hf).elim

theorem wire_wall_collar_off_lane (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) (c : PrimitiveCode)
    (hc : c ∈ wireCodes w q)
    (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height)
    (hp : p ∈ (c.instanceOf w hw).board.walls) (face : Direction)
    (hf : InCollar w face (c.world w hw p)) :
    ¬SameLane face (Line.along w face (boundaryPoint w face) 0) (c.world w hw p) := by
  change c ∈ (wireSpec w q).codes at hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases ((wireSpec w q).mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · exact centered_wall_collar_off_lane w hw _ ((wireSpec w q).line_good w (wireSpec_geometry w q) i hi')
      (wire_line_centered w q i hi') p hp face hf
  · exact ((interior_not_collar w face (wire_turn_window_interior w hw q i ht p)) hf).elim

end PushPuzzle.PushS.FiniteRouting
