/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionEndBand
public import PushS.FiniteRoutingActionPath
public import PushS.FiniteRoutingNormalWalking
public import PushS.FiniteTurnDockMacros
public import PushS.FiniteRoutingOuterLanes
public import PushS.FiniteRoutingWorldCoordinates

/-! The turn's open access rectangle is literal exposed interior floor of its actual incoming line. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side

namespace Turn

/-- The open rectangle connecting the incoming and outgoing turn lanes. -/
def accessRegion (w : ℕ) : Finset (Cell (FiniteTools.side w) (FiniteTools.side w)) :=
  Finset.univ.filter fun p => FiniteTools.radius w-w-1 ≤ p.1.val ∧ p.1.val ≤ FiniteTools.radius w-3 ∧
    FiniteTools.radius w+3 ≤ p.2.val ∧ p.2.val ≤ FiniteTools.radius w+w+1

theorem mem_accessRegion (w : ℕ) (p : Cell (FiniteTools.side w) (FiniteTools.side w)) :
    p ∈ accessRegion w ↔ FiniteTools.radius w-w-1 ≤ p.1.val ∧ p.1.val ≤ FiniteTools.radius w-3 ∧
      FiniteTools.radius w+3 ≤ p.2.val ∧ p.2.val ≤ FiniteTools.radius w+w+1 := by
  simp only [accessRegion,Finset.mem_filter,Finset.mem_univ,true_and]

/-- The common outer-lane corner of the turn access rectangle. -/
@[expose] def accessCorner (w : ℕ) : Cell (FiniteTools.side w) (FiniteTools.side w) :=
  (⟨FiniteTools.radius w-w-1,by unfold FiniteTools.side FiniteTools.radius; omega⟩,
   ⟨FiniteTools.radius w+w+1,by unfold FiniteTools.side FiniteTools.radius; omega⟩)

theorem accessCorner_mem (w : ℕ) (hw : 2 ≤ w) : accessCorner w ∈ accessRegion w := by
  rw [mem_accessRegion]
  dsimp [accessCorner]
  unfold FiniteTools.radius
  omega

theorem dock_mem (w : ℕ) (hw : 2 ≤ w) : FiniteTools.turnDock w ∈ accessRegion w := by
  rw [mem_accessRegion]
  dsimp [FiniteTools.turnDock]
  unfold FiniteTools.radius
  omega

end Turn

/-- The incoming-line cell representing a point in the turn access rectangle. -/
@[expose] def turnIncomingCell (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment) (t : TurnCode)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ Turn.accessRegion w) :
    Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w) :=
  (⟨segmentLength c.segment+2+p.1.val,by
      have hb := (Turn.mem_accessRegion w p).mp hp
      have hspan := Line.program_span_of_bound w _ (c.above != c.desiredSide) hc.2.1
      unfold Line.width
      unfold FiniteTools.radius at *
      omega⟩,
   ⟨if t.outgoing = rightTurn t.incoming then p.2.val else FiniteTools.side w-(p.2.val+1),by
      have hb := p.2.isLt
      unfold Line.height
      change _ < FiniteTools.side w
      split_ifs <;> unfold FiniteTools.side FiniteTools.radius at * <;> omega⟩)

theorem turnIncomingCell_bounds (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment) (t : TurnCode)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ Turn.accessRegion w) :
    let q := turnIncomingCell w hw c hc t p hp
    FiniteTools.radius w+1 ≤ q.1.val ∧
      q.1.val ≤ FiniteTools.radius w+Line.span w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) ∧
      FiniteTools.radius w-w-1 ≤ q.2.val ∧ q.2.val ≤ FiniteTools.radius w+w+1 ∧ q.2.val ≠ FiniteTools.radius w := by
  have hb := (Turn.mem_accessRegion w p).mp hp
  have hl := hc.2.1
  have hspan := Line.program_span_of_bound w _ (c.above != c.desiredSide) hc.2.1
  dsimp [turnIncomingCell]
  split_ifs <;> unfold FiniteTools.side FiniteTools.radius at * <;> omega

private theorem turnIncomingCell_floor (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment) (t : TurnCode)
    (hside : c.desiredSide = turnSide t.incoming t.outgoing)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ Turn.accessRegion w) :
    turnIncomingCell w hw c hc t p hp ∉ Line.walls w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above := by
  intro hwall
  have hb := (Turn.mem_accessRegion w p).mp hp
  have hspan := Line.program_span_of_bound w _ (c.above != c.desiredSide) hc.2.1
  have hx : FiniteTools.radius w+Line.span w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) ≤
      (turnIncomingCell w hw c hc t p hp).1.val+(w+1) := by
    dsimp [turnIncomingCell]
    unfold FiniteTools.radius at *
    omega
  have hband := Line.program_end_wall_band w _ (c.above != c.desiredSide) c.above _ hwall hx
  have hs : Line.exitSide c.above (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) = turnSide t.incoming t.outgoing := by
    rw [←hside]
    cases c.above <;> cases c.desiredSide <;> simp [Line.program_exitSide]
  rw [hs] at hband
  by_cases ht : t.outgoing = rightTurn t.incoming
  · simp only [Line.StockBand,turnSide,ht,decide_true,↓reduceIte] at hband
    dsimp [turnIncomingCell] at hband
    simp only [ht,↓reduceIte] at hband
    omega
  · simp only [Line.StockBand,turnSide,ht,decide_false] at hband
    dsimp [turnIncomingCell] at hband
    simp only [ht,↓reduceIte] at hband
    unfold FiniteTools.side FiniteTools.radius at *
    omega

theorem turnIncomingCell_active (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment) (t : TurnCode)
    (hside : c.desiredSide = turnSide t.incoming t.outgoing)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ Turn.accessRegion w) :
    turnIncomingCell w hw c hc t p hp ∈ Line.Action.active w
      (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last := by
  have hb := turnIncomingCell_bounds w hw c hc t p hp
  apply Finset.mem_filter.mpr
  refine ⟨?_,Or.inr (Or.inl ⟨hb.1,hb.2.1⟩)⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,by omega,hb.2.1.trans (by omega),hb.2.2.1,hb.2.2.2.1,turnIncomingCell_floor w hw c hc t hside p hp⟩

-- The eight oriented coordinate cases normalize dependent line and turn embeddings.
set_option maxHeartbeats 1000000 in
theorem turnIncomingCell_world (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment) (t : TurnCode)
    (hd : segmentDirection c.segment = t.incoming)
    (hf : c.segment.finish = advance t.incoming.opposite t.corner 2)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ Turn.accessRegion w) :
    c.actionWorld w hw (turnIncomingCell w hw c hc t p hp) =
      (PrimitiveCode.turn t).world w hw ((Turn.orientation w t.incoming t.outgoing).cells p) := by
  let q := turnIncomingCell w hw c hc t p hp
  change c.actionWorld w hw q = t.actionWorld w hw p
  rw [LineCode.actionWorld_eq,TurnCode.actionWorld_eq]
  simp only [coordinates]
  have htravel := segment_travels c.segment hc.1
  rw [hd,hf] at htravel
  have hb := (Turn.mem_accessRegion w p).mp hp
  have hlength := hc.2.1
  have hspan := Line.program_span_of_bound w _ (c.above != c.desiredSide) hc.2.1
  by_cases hs : t.outgoing = rightTurn t.incoming
  all_goals simp only [q,turnIncomingCell,hs,↓reduceIte,hd,Line.rotatedCoordinates]
  all_goals cases di : t.incoming
  all_goals simp only [di] at htravel ⊢
  all_goals dsimp [Line.rotatedCoordinates,Line.offsetX,Line.offsetY,Line.anchor] at htravel ⊢
  all_goals dsimp [Turn.quarterCoordinates,Turn.offsetX,Turn.offsetY,Travels,advance,Direction.opposite] at htravel ⊢
  all_goals apply Prod.ext
  all_goals simp only [Line.width,Line.height,FiniteTools.side,FiniteTools.radius,padding] at *
  all_goals omega

theorem turnIncomingCell_corner_lane (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment) (t : TurnCode) :
    let q := turnIncomingCell w hw c hc t (Turn.accessCorner w) (Turn.accessCorner_mem w hw)
    q = Line.outerCell w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))
      (!(turnSide t.incoming t.outgoing)) q.1 := by
  dsimp only
  apply Prod.ext
  · rfl
  · apply Fin.ext
    by_cases hs : t.outgoing = rightTurn t.incoming
    all_goals simp [turnIncomingCell,Turn.accessCorner,Line.outerCell,Line.laneY,turnSide,hs]
    unfold FiniteTools.side FiniteTools.radius
    omega

-- The perpendicular directions leave eight affine cases with truncated natural subtraction.
set_option maxHeartbeats 1000000 in
theorem turnOutgoingCorner_world (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment) (t : TurnCode)
    (ht : Perpendicular t.incoming t.outgoing) (hd : segmentDirection c.segment = t.outgoing)
    (hs : c.segment.start = advance t.outgoing t.corner 1) :
    c.laneWorld w hw hc (!(turnSide t.incoming t.outgoing)) w (by have h := hc.2.1; omega) =
      (PrimitiveCode.turn t).world w hw ((Turn.orientation w t.incoming t.outgoing).cells (Turn.accessCorner w)) := by
  change c.laneWorld w hw hc (!(turnSide t.incoming t.outgoing)) w _ =
    t.actionWorld w hw (Turn.accessCorner w)
  rw [LineCode.laneWorld_eq,hd,hs,TurnCode.actionWorld_eq]
  simp only [coordinates]
  have htravel := segment_travels c.segment hc.1
  rw [hd,hs] at htravel
  have hlength := hc.2.1
  cases di : t.incoming <;> cases dout : t.outgoing <;>
    simp [di,dout,Perpendicular,rightTurn,Direction.opposite] at ht <;>
    simp only [dout] at htravel ⊢ <;>
    dsimp [Line.outerAlong,Turn.quarterCoordinates,Turn.accessCorner,Turn.offsetX,Turn.offsetY,
      turnSide,rightTurn,Travels,advance,Direction.opposite] at htravel ⊢ <;> apply Prod.ext <;>
    simp only [FiniteTools.side,FiniteTools.radius,padding] at * <;> omega

end PushPuzzle.PushS.FiniteRouting
