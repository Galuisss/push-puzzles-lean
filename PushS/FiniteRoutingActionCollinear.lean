/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionCoordinates
public import PushS.FiniteRoutingWorldCoordinates
public import PushS.FiniteRoutingActionGuards

/-! Actual stock guards exclude every foreign wall across a collinear route seam. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls Line.program Line.span FiniteTools.side

private theorem band_ne_row {w : ℕ} {above : Bool} {y : ℕ} (h : Line.StockBand w above y) :
    y ≠ FiniteTools.radius w := by
  cases above <;> dsimp [Line.StockBand] at h <;> omega

private theorem band_not_exposed {w : ℕ} {above : Bool} {y : ℕ} (h : Line.StockBand w above y) :
    ¬Line.Exposed w above y := by
  cases above <;> dsimp [Line.StockBand,Line.Exposed] at * <;> omega

private theorem program_side (w length : ℕ) (above desired : Bool) :
    Line.exitSide above (Line.program w length (above != desired)) = desired := by
  cases above <;> cases desired <;> simp [Line.program_exitSide]

theorem collinear_action_ne_next_wall (w : ℕ) (hw : 2 ≤ w) (c e : LineCode)
    (hc : LineGood w c.segment) (he : LineGood w e.segment)
    (hd : segmentDirection c.segment = segmentDirection e.segment) (hj : c.segment.finish = e.segment.start)
    (hside : c.desiredSide = e.above)
    : c.ActionClear w hw e := by
  let ca := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let ea := Line.program w (segmentLength e.segment) (e.above != e.desiredSide)
  have hlen : Line.span w ca = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  intro p hp q hq
  obtain ⟨a,ha,heq⟩ := e.wall_world w hw q hq
  obtain ⟨hu,hb⟩ := (Line.Action.mem_active w ca c.above c.last p).mp hp
  intro h
  rw [heq] at h
  have hh := c.collinear_action_coordinates w hw e hc he hd hj p a h
  have haB := Line.walls_bounds w ea e.above ha
  have hnear : a.1.val < FiniteTools.radius w+2*Line.buffer w := by
    have hmax := hb.2.1
    rw [hlen] at hmax
    unfold Line.buffer
    omega
  have hbandA := Line.program_first_wall_band w (segmentLength e.segment) (e.above != e.desiredSide) e.above a ha hnear
  have hband : Line.StockBand w (Line.exitSide c.above ca) p.2.val := by
    have hs : Line.exitSide c.above ca = e.above := (program_side w _ _ _).trans hside
    rw [hs,hh.2]
    exact hbandA
  have hup : p.1.val ≤ FiniteTools.radius w+Line.span w ca := by
    rcases hu with hu | hu | hu
    · exact (band_ne_row hband hu.1).elim
    · exact hu.2
    · exact (band_not_exposed hband hu.2.2).elim
  apply hb.2.2.2.2
  exact Line.program_last_stock_wall w (segmentLength c.segment) (c.above != c.desiredSide) c.above p
    (by rw [hlen]; have hhx := haB.1; omega)
    (by change p.1.val < FiniteTools.radius w+Line.span w ca+2; omega) hband

theorem collinear_action_ne_previous_wall (w : ℕ) (hw : 2 ≤ w) (e c : LineCode)
    (he : LineGood w e.segment) (hc : LineGood w c.segment)
    (hd : segmentDirection e.segment = segmentDirection c.segment) (hj : e.segment.finish = c.segment.start)
    (hside : e.desiredSide = c.above)
    : c.ActionClear w hw e := by
  let ca := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let ea := Line.program w (segmentLength e.segment) (e.above != e.desiredSide)
  have hlen : Line.span w ea = segmentLength e.segment := Line.program_span_of_bound w _ _ he.2.1
  intro p hp q hq
  obtain ⟨a,ha,heq⟩ := e.wall_world w hw q hq
  obtain ⟨hu,hb⟩ := (Line.Action.mem_active w ca c.above c.last p).mp hp
  intro h
  rw [heq] at h
  have hh := e.collinear_action_coordinates w hw c he hc hd hj a p h.symm
  have haB := Line.walls_bounds w ea e.above ha
  have hpX : FiniteTools.radius w ≤ p.1.val := by rcases hu with hu | hu | hu <;> omega
  have hbandA := Line.program_last_wall_band w (segmentLength e.segment) (e.above != e.desiredSide) e.above a ha
    (by rw [hlen]; omega)
  have hband : Line.StockBand w c.above p.2.val := by
    have hs : Line.exitSide e.above ea = c.above := (program_side w _ _ _).trans hside
    change Line.StockBand w (Line.exitSide e.above ea) a.2.val at hbandA
    rwa [hs,hh.2] at hbandA
  apply hb.2.2.2.2
  exact Line.program_first_stock_wall w (segmentLength c.segment) (c.above != c.desiredSide) c.above p hpX (by
    have hmax := haB.2.1
    rw [hlen] at hmax
    unfold Line.buffer
    omega) hband

end PushPuzzle.PushS.FiniteRouting
