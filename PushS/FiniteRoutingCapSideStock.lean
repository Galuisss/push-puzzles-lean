/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingSideCollars

/-! A terminal line extends its exposed side band through the final cap. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

namespace LineCode

theorem cap_side_band_of_cell (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w))
    (hx : FiniteTools.radius w+1 ≤ p.1.val)
    (hy : p.2.val ≠ FiniteTools.radius w) : CapSideBand w c (c.actionWorld w hw p) := by
  have ht := segment_travels c.segment hc.1
  rw [c.actionWorld_native w hw hc p]
  have ⟨hpx,hpy⟩ := c.action_cell_bounds w hc p
  have hlen := Line.program_span_of_bound w _ (c.above != c.desiredSide) hc.2.1
  cases hd : segmentDirection c.segment <;> simp only [CapSideBand,hd] at ht ⊢ <;>
    dsimp [Outward,SameLane,Travels,Line.along,Direction.opposite] at ht ⊢ <;>
    simp only [FiniteTools.radius,hlen,padding] at * <;> omega

end LineCode

theorem local_cap_side_actor_ne (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : LineCode)
    (hc : .line c ∈ FiniteSourceInventory.localCodes w code)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w))
    (hp : c.NearTrace w (c.actionWorld w hw p))
    (ha : CapSideBand w c (c.actionWorld w hw p)) (hlast : c.last = true)
    (d : PrimitiveCode) (hd : d ∈ FiniteSourceInventory.localCodes w code) (goal : Bool) (l : d.Labels w) :
    c.actionWorld w hw p ≠ d.actor w hw goal l := by
  exact local_side_actor_ne_of_guard w hw code c hc p hp ha
    (fun hf => by rw [hlast] at hf; cases hf) d hd goal l

end PushPuzzle.PushS.FiniteRouting
