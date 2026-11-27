/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionFootprint

/-! Literal canonical coordinates agree across a collinear pair's actual rectangle placements. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.LineCode

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls Line.program Line.span FiniteTools.side

theorem collinear_action_coordinates (w : ℕ) (hw : 2 ≤ w) (c e : LineCode)
    (hc : LineGood w c.segment) (he : LineGood w e.segment)
    (hd : segmentDirection c.segment = segmentDirection e.segment) (hj : c.segment.finish = e.segment.start)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w))
    (q : Cell (Line.width w (Line.program w (segmentLength e.segment) (e.above != e.desiredSide))) (Line.height w))
    (ha : c.actionWorld w hw p = e.actionWorld w hw q) :
    p.1.val = segmentLength c.segment+q.1.val ∧ p.2.val = q.2.val := by
  let ca := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let ea := Line.program w (segmentLength e.segment) (e.above != e.desiredSide)
  have hcspan : Line.span w ca = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  have hespan : Line.span w ea = segmentLength e.segment := Line.program_span_of_bound w _ _ he.2.1
  have hcLit : Line.span w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) = segmentLength c.segment := hcspan
  have heLit : Line.span w (Line.program w (segmentLength e.segment) (e.above != e.desiredSide)) = segmentLength e.segment := hespan
  have hcRot := Line.rotation_coordinates w ca (segmentDirection c.segment) p
  have heRot := Line.rotation_coordinates w ea (segmentDirection e.segment) q
  have hcX := congrArg Prod.fst hcRot
  have hcY := congrArg Prod.snd hcRot
  have heX := congrArg Prod.fst heRot
  have heY := congrArg Prod.snd heRot
  dsimp only [coordinates] at hcX hcY heX heY
  have hx := congrArg Prod.fst ha
  have hy := congrArg Prod.snd ha
  change Line.offsetX w ca (segmentDirection c.segment) c.segment.start+
      ((Line.rotation w ca (segmentDirection c.segment)).cells p).1.val =
    Line.offsetX w ea (segmentDirection e.segment) e.segment.start+
      ((Line.rotation w ea (segmentDirection e.segment)).cells q).1.val at hx
  change Line.offsetY w ca (segmentDirection c.segment) c.segment.start+
      ((Line.rotation w ca (segmentDirection c.segment)).cells p).2.val =
    Line.offsetY w ea (segmentDirection e.segment) e.segment.start+
      ((Line.rotation w ea (segmentDirection e.segment)).cells q).2.val at hy
  rw [hcX,heX,←hd,←hj] at hx
  rw [hcY,heY,←hd,←hj] at hy
  have ht := segment_travels c.segment hc.1
  have ht' := segment_travels e.segment he.1
  rw [←hd,←hj] at ht'
  have hpx := p.1.isLt
  have hpy := p.2.isLt
  have hqx := q.1.isLt
  have hqy := q.2.isLt
  clear ha hcRot heRot hcX hcY heX heY
  cases hdir : segmentDirection c.segment <;> simp only [hdir] at ht ht' hx hy
  all_goals dsimp [Line.rotatedCoordinates,Line.offsetX,Line.offsetY,Line.anchor,Travels] at ht ht' hx hy
  all_goals simp only [Line.width,Line.height,FiniteTools.side,FiniteTools.radius,hcspan,hespan,hcLit,heLit,padding]
    at ht ht' hx hy hpx hpy hqx hqy
  all_goals constructor <;> omega

end PushPuzzle.PushS.FiniteRouting.LineCode
