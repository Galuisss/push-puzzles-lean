/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionSeams
public import PushS.FiniteRoutingOuterContacts
public import PushS.FiniteRoutingBandContacts

/-! Every possible foreign contact of an actual line action lies at a reciprocal source port. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls Line.program Line.span FiniteTools.side

private theorem band_of_portCoordinates (w margin : ℕ) (face : Direction) (a : ℕ × ℕ)
    (hb : -(margin : ℤ) ≤ (portCoordinates w (0,0) face a).2 ∧
      (portCoordinates w (0,0) face a).2 ≤ margin) : PortBand w margin face a := by
  cases face <;> dsimp [portCoordinates,macroShift,Line.along,boundaryPoint,PortBand] at * <;> omega

theorem LinePort.action_band (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (face : Direction) (incoming : Bool) (hport : LinePort w c face incoming) (p : c.ActionCell w)
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last) :
    PortBand w (w+1) face (c.actionWorld w hw p) := by
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hy0 := hb.2.2.1
  have hy1 := hb.2.2.2.1
  apply band_of_portCoordinates w (w+1) face
  rcases hport with ⟨hd,he,_,_⟩ | ⟨_,hd,he,_⟩
  · have heq := c.portCoordinates_end w hw hc (0,0) face incoming hd he p
    simp only [macroShift,Nat.mul_zero,Nat.zero_add] at heq
    rw [heq]
    dsimp only
    unfold FiniteTools.radius at *
    omega
  · have heq := c.portCoordinates_start w hw hc (0,0) face hd he p
    simp only [macroShift,Nat.mul_zero,Nat.zero_add] at heq
    rw [heq]
    dsimp only
    unfold FiniteTools.radius at *
    omega

end PushPuzzle.PushS.FiniteRouting
