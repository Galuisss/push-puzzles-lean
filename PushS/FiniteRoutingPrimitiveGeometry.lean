/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPieces
public import PushS.FiniteRoutingDirections
public import PushS.FiniteRoutingClearance

/-! Coordinates and literal path footprints of the semantic primitive inventories. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

attribute [local irreducible] Line.width Line.height Line.walls FiniteGeometry.side FiniteTools.side

namespace PrimitiveCode

/-- Coordinates after the actual translation used by both inventory assembly and bitmap emission. -/
def world (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode)
    (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height) : ℕ × ℕ :=
  (c.offsetX w+p.1.val,c.offsetY w+p.2.val)

def actor (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) (goal : Bool) (l : c.Labels w) : ℕ × ℕ :=
  c.world w hw (if goal then (c.matching w hw).target l else (c.matching w hw).source l)

end PrimitiveCode

def LineGood (w : ℕ) (s : Segment) : Prop :=
  (s.start.1 = s.finish.1 ∨ s.start.2 = s.finish.2) ∧
    17*w+61 ≤ segmentLength s ∧
    (s.start.1 ≤ tileStride w ∧ s.start.2 ≤ tileStride w) ∧
    (s.finish.1 ≤ tileStride w ∧ s.finish.2 ≤ tileStride w)

theorem trimmedSegment_lineGood (w : ℕ) (segments : List Segment)
    (hg : ∀ s ∈ segments, SegmentGood w s) (i : ℕ) (hi : i < segments.length) :
    LineGood w (trimmedSegment segments i) :=
  trimmedSegment_good w segments hg i hi

private theorem line_travels (w : ℕ) (c : LineCode) (hg : LineGood w c.segment) :
    Travels (segmentDirection c.segment) c.segment.start c.segment.finish
      (Line.span w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) := by
  rw [Line.program_span_of_bound w _ _ hg.2.1]
  exact segment_travels c.segment hg.1

theorem line_actor (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hg : LineGood w c.segment)
    (goal : Bool) (l : (PrimitiveCode.line c).Labels w) :
    (PrimitiveCode.line c).actor w hw goal l =
      Line.along w (segmentDirection c.segment) c.segment.start
        (Line.position w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))
          (if goal then c.target else c.initial) l.val) := by
  cases goal <;>
    exact Line.placement_cell w hw _ _ _ _ (line_travels w c hg) hg.2.2.1 hg.2.2.2 _ l.val

/-- The actual matched normal actor, rather than a proxy centerline point, has this footprint. -/
theorem line_actor_footprint (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hg : LineGood w c.segment)
    (goal : Bool) (l : (PrimitiveCode.line c).Labels w) :
    ∃ u, c.segment.Contains u ∧
      Nearby 1 ((PrimitiveCode.line c).actor w hw goal l) (padding w+u.1,padding w+u.2) := by
  cases goal <;>
    exact Line.placed_box_footprint w hw _ _ _ _ (line_travels w c hg) hg.2.2.1 hg.2.2.2 _ l.val

theorem line_wall_footprint (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hg : LineGood w c.segment)
    (p : Cell
      (Line.orientedWidth w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))
        (segmentDirection c.segment))
      (Line.orientedHeight w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))
        (segmentDirection c.segment)))
    (hp : p ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) :
    ∃ u, c.segment.Contains u ∧
      Nearby (w+1) ((PrimitiveCode.line c).world w hw p) (padding w+u.1,padding w+u.2) := by
  change p ∈ (Line.walls w
    (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above).map
      (Line.rotation w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))
        (segmentDirection c.segment)).cells.toEmbedding at hp
  simp only [Finset.mem_map] at hp
  obtain ⟨a,ha,he⟩ := hp
  have hlen := Line.program_span_of_bound w (segmentLength c.segment) (c.above != c.desiredSide) hg.2.1
  with_reducible have hb := (Line.walls_bounds w
    (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above (p := a) ha)
  rw [hlen] at hb
  let t := min (a.1.val-FiniteTools.radius w) (segmentLength c.segment)
  have ht : t ≤ segmentLength c.segment := min_le_right _ _
  have htr := segment_travels c.segment hg.1
  refine ⟨advance (segmentDirection c.segment) c.segment.start t,
    advance_contains _ _ _ _ t htr ht,?_⟩
  have hr := Line.rotation_coordinates w
    (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) (segmentDirection c.segment) a
  have hrx := congrArg Prod.fst hr
  have hry := congrArg Prod.snd hr
  have hex := congrArg (fun z => z.1.val) he
  have hey := congrArg (fun z => z.2.val) he
  dsimp only at hrx hry hex hey
  change ((Line.rotation w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))
    (segmentDirection c.segment)).cells a).1.val = p.1.val at hex
  change ((Line.rotation w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))
    (segmentDirection c.segment)).cells a).2.val = p.2.val at hey
  dsimp only [PrimitiveCode.world,PrimitiveCode.offsetX,PrimitiveCode.offsetY]
  rw [←hex,←hey,hrx,hry]
  have haX := a.1.isLt
  have haY := a.2.isLt
  cases hd : segmentDirection c.segment <;>
    simp only [hd] at * <;>
    dsimp [t,Line.rotatedCoordinates,Nearby,advance,Travels,Line.offsetX,Line.offsetY,Line.anchor] at * <;>
    unfold Line.width Line.height FiniteTools.side FiniteTools.radius padding at * <;>
    simp only [hlen] at * <;> omega

namespace Turn

def quarterCoordinates (w : ℕ) (d : Direction) (p : ℕ × ℕ) : ℕ × ℕ :=
  match d with
  | .east => p
  | .south => (FiniteTools.side w-(p.2+1),p.1)
  | .west => (FiniteTools.side w-(p.1+1),FiniteTools.side w-(p.2+1))
  | .north => (p.2,FiniteTools.side w-(p.1+1))

private theorem quarter_coordinates (w : ℕ) (d : Direction)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) :
    coordinates ((quarter w d).cells p) = quarterCoordinates w d (coordinates p) := by
  cases d <;> rfl

theorem orientation_coordinates (w : ℕ) (d e : Direction)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) :
    coordinates ((orientation w d e).cells p) = quarterCoordinates w d
      (if e = rightTurn d then coordinates p else (p.1.val,FiniteTools.side w-(p.2.val+1))) := by
  unfold orientation
  split_ifs
  · exact quarter_coordinates w d p
  · change coordinates ((quarter w d).cells ((GridIsometry.reflectY _ _).cells p)) = _
    rw [quarter_coordinates]
    cases d <;> rfl

end Turn

private theorem turn_actor_unfold (w : ℕ) (hw : 2 ≤ w) (c : TurnCode) (goal : Bool) (l : Fin 2) :
    (PrimitiveCode.turn c).actor w hw goal l =
      (Turn.offsetX w c.corner+
        ((Turn.orientation w c.incoming c.outgoing).cells (Turn.cell w (if goal then c.target else c.initial) l)).1.val,
       Turn.offsetY w c.corner+
        ((Turn.orientation w c.incoming c.outgoing).cells (Turn.cell w (if goal then c.target else c.initial) l)).2.val) := by
  cases goal <;> rfl

set_option maxRecDepth 65536 in
/-- The two owned turn actors are exactly the incoming F and outgoing G slots. -/
theorem turn_actor (w : ℕ) (hw : 2 ≤ w) (c : TurnCode) (hc : Perpendicular c.incoming c.outgoing)
    (goal : Bool) (l : Fin 2) :
    (PrimitiveCode.turn c).actor w hw goal l =
      if l = 0 then Line.along w c.incoming.opposite c.corner
        (2-(if goal then c.target else c.initial).toNat)
      else Line.along w c.outgoing c.corner (1+(if goal then c.target else c.initial).toNat) := by
  rw [turn_actor_unfold]
  have hr := Turn.orientation_coordinates w c.incoming c.outgoing
    (Turn.cell w (if goal then c.target else c.initial) l)
  have hx := congrArg Prod.fst hr
  have hy := congrArg Prod.snd hr
  dsimp only [coordinates] at hx hy
  rw [hx,hy]
  rcases c with ⟨d,e,p,a,b⟩
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  cases goal <;> cases d <;> cases e <;> fin_cases l <;>
    simp [Perpendicular,rightTurn,Direction.opposite] at hc <;>
    dsimp [Turn.quarterCoordinates,Turn.cell,Turn.label,rightTurn,coordinates,
      FiniteTools.turnMixedCell,FiniteTools.turnMixedPoint,Line.along,Direction.opposite,
      Turn.offsetX,Turn.offsetY] <;>
    apply Prod.ext <;>
    simp only [FiniteTools.side,FiniteTools.radius,padding] <;> omega

theorem turn_actor_footprint (w : ℕ) (hw : 2 ≤ w) (c : TurnCode)
    (hc : Perpendicular c.incoming c.outgoing) (goal : Bool) (l : Fin 2) :
    Nearby 2 ((PrimitiveCode.turn c).actor w hw goal l) (padding w+c.corner.1,padding w+c.corner.2) := by
  rw [turn_actor w hw c hc goal l]
  have hi := Bool.toNat_le c.initial
  have ht := Bool.toNat_le c.target
  split_ifs <;> cases c.incoming <;> cases c.outgoing <;>
    dsimp [Nearby,Line.along,Direction.opposite] <;> omega

theorem turn_window_footprint (w : ℕ) (hw : 2 ≤ w) (c : TurnCode)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) :
    Nearby (FiniteTools.radius w) ((PrimitiveCode.turn c).world w hw p)
      (padding w+c.corner.1,padding w+c.corner.2) := by
  have hx := p.1.isLt
  have hy := p.2.isLt
  dsimp [Nearby,PrimitiveCode.world,PrimitiveCode.offsetX,PrimitiveCode.offsetY,Turn.offsetX,Turn.offsetY]
  unfold FiniteTools.side FiniteTools.radius padding at *
  omega

theorem directions_chain_adjacent (segments : List Segment)
    (hc : (segments.map segmentDirection).IsChain (fun d e => d = e ∨ Perpendicular d e))
    (i : ℕ) (hi : i+1 < segments.length) :
    segmentDirection (segmentAt segments i) = segmentDirection (segmentAt segments (i+1)) ∨
      Perpendicular (segmentDirection (segmentAt segments i)) (segmentDirection (segmentAt segments (i+1))) := by
  have h := hc.getElem i (by simpa only [List.length_map] using hi)
  simpa only [List.getElem_map,segmentAt,List.getD_eq_getElem _ _ (by omega : i < segments.length),
    List.getD_eq_getElem _ _ hi] using h

private theorem pathCodes_turn_perpendicular (segments : List Segment)
    (hc : (segments.map segmentDirection).IsChain (fun d e => d = e ∨ Perpendicular d e))
    (initialSide targetSide keepEndpoint initial target : Bool) (c : TurnCode)
    (hm : PrimitiveCode.turn c ∈ pathCodes segments initialSide targetSide keepEndpoint initial target) :
    Perpendicular c.incoming c.outgoing := by
  obtain ⟨i,hi,hm⟩ := List.mem_flatMap.mp hm
  rcases List.mem_append.mp hm with hm | hm
  · simp at hm
  · split_ifs at hm with ht
    · have he := List.mem_singleton.mp hm
      cases he
      exact (directions_chain_adjacent segments hc i ht.1).resolve_left ht.2
    · simp at hm

theorem wireCodes_turn_perpendicular (w : ℕ) (q : Catalog.Bitmap.Args) (c : TurnCode)
    (hc : PrimitiveCode.turn c ∈ wireCodes w q) : Perpendicular c.incoming c.outgoing :=
  pathCodes_turn_perpendicular _ (wireRoute_directions_chain w q.1) _ _ _ _ _ c hc

private theorem segmentAt_mem (segments : List Segment) (i : ℕ) (hi : i < segments.length) :
    segmentAt segments i ∈ segments := by
  rw [segmentAt,List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

private theorem pathCodes_line_good (w : ℕ) (segments : List Segment)
    (hg : ∀ s ∈ segments, SegmentGood w s)
    (initialSide targetSide keepEndpoint initial target : Bool) (c : LineCode)
    (hm : PrimitiveCode.line c ∈ pathCodes segments initialSide targetSide keepEndpoint initial target) :
    LineGood w c.segment ∧ c.first = false ∧ c.initial = initial ∧ c.target = target ∧
      ∀ u, c.segment.Contains u → ∃ s ∈ segments, s.Contains u := by
  obtain ⟨i,hi,hm⟩ := List.mem_flatMap.mp hm
  have hi' := List.mem_range.mp hi
  rcases List.mem_append.mp hm with hm | hm
  · have he := List.mem_singleton.mp hm
    cases he
    refine ⟨trimmedSegment_lineGood w segments hg i hi',rfl,rfl,rfl,?_⟩
    intro u hu
    have hs := hg _ (segmentAt_mem segments i hi')
    refine ⟨segmentAt segments i,segmentAt_mem segments i hi',?_⟩
    exact trimmed_trace_subset _ hs.1 _ _
      (by have hf := startTrim_bound segments i; have hb := finishTrim_bound segments i
          have hl := hs.2.1; omega) hu
  · split_ifs at hm <;> simp at hm

theorem gateCodes_line_good (w : ℕ) (g : GateTileState) (c : LineCode)
    (hc : PrimitiveCode.line c ∈ gateCodes w g) : LineGood w c.segment ∧ c.first = false := by
  rcases List.mem_cons.mp hc with hc | hc
  · simp at hc
  · obtain ⟨role,_,hc⟩ := List.mem_flatMap.mp hc
    have h := pathCodes_line_good w _ (armRoute_good w g role) _ _ _ _ _ c hc
    exact ⟨h.1,h.2.1⟩

theorem wireCodes_line_good (w : ℕ) (q : Catalog.Bitmap.Args) (c : LineCode)
    (hc : PrimitiveCode.line c ∈ wireCodes w q) : LineGood w c.segment ∧ c.first = false := by
  have h := pathCodes_line_good w _ (wireRoute_good w q.1) _ _ _ _ _ c hc
  exact ⟨h.1,h.2.1⟩

end PushPuzzle.PushS.FiniteRouting
