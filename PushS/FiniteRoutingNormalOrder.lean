/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingGateRows
public import PushS.FiniteRoutingLineCut

/-! Literal initial and target slots retain every coordinate order inside a line or turn primitive. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

theorem line_actor_order (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (l r : (PrimitiveCode.line c).Labels w) :
    (((PrimitiveCode.line c).actor w hw false l).1 < ((PrimitiveCode.line c).actor w hw false r).1 →
      ((PrimitiveCode.line c).actor w hw true l).1 < ((PrimitiveCode.line c).actor w hw true r).1) ∧
    (((PrimitiveCode.line c).actor w hw false l).2 < ((PrimitiveCode.line c).actor w hw false r).2 →
      ((PrimitiveCode.line c).actor w hw true l).2 < ((PrimitiveCode.line c).actor w hw true r).2) := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have hlen : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  have ht := segment_travels c.segment hc.1
  have hbound (q : Bool) (a : Line.Label w atoms) : Line.position w atoms q a ≤ segmentLength c.segment+1 := by
    have h := Line.positions_bounds w hw q atoms (Line.position_mem w atoms q a)
    have hp := Bool.toNat_le q
    rw [hlen] at h
    omega
  have hli := hbound c.initial l.val
  have hri := hbound c.initial r.val
  have hlt := hbound c.target l.val
  have hrt := hbound c.target r.val
  dsimp only [atoms] at hli hri hlt hrt
  constructor <;> intro ho
  all_goals rw [line_actor w hw c hc false l,line_actor w hw c hc false r] at ho
  all_goals rw [line_actor w hw c hc true l,line_actor w hw c hc true r]
  all_goals rcases lt_trichotomy l.val.val r.val.val with h | h | h
  all_goals first
  | have ha := Line.position_gap w hw atoms c.initial l.val r.val h
    have hb := Line.position_gap w hw atoms c.target l.val r.val h
    dsimp only [atoms] at ha hb
    cases hd : segmentDirection c.segment <;> simp only [hd] at ht ho ⊢ <;>
      dsimp [Line.along,Travels] at * <;> unfold padding at * <;> omega
  | have he : l = r := Subtype.ext (Fin.ext h)
    subst r
    omega
  | have ha := Line.position_gap w hw atoms c.initial r.val l.val h
    have hb := Line.position_gap w hw atoms c.target r.val l.val h
    dsimp only [atoms] at ha hb
    cases hd : segmentDirection c.segment <;> simp only [hd] at ht ho ⊢ <;>
      dsimp [Line.along,Travels] at * <;> unfold padding at * <;> omega

theorem turn_actor_order (w : ℕ) (hw : 2 ≤ w) (c : TurnCode) (hc : Perpendicular c.incoming c.outgoing)
    (l r : Fin 2) :
    (((PrimitiveCode.turn c).actor w hw false l).1 < ((PrimitiveCode.turn c).actor w hw false r).1 →
      ((PrimitiveCode.turn c).actor w hw true l).1 < ((PrimitiveCode.turn c).actor w hw true r).1) ∧
    (((PrimitiveCode.turn c).actor w hw false l).2 < ((PrimitiveCode.turn c).actor w hw false r).2 →
      ((PrimitiveCode.turn c).actor w hw true l).2 < ((PrimitiveCode.turn c).actor w hw true r).2) := by
  have hi := Bool.toNat_le c.initial
  have ht := Bool.toNat_le c.target
  constructor <;> intro ho
  all_goals rw [turn_actor w hw c hc false l,turn_actor w hw c hc false r] at ho
  all_goals rw [turn_actor w hw c hc true l,turn_actor w hw c hc true r]
  all_goals fin_cases l <;> fin_cases r <;> cases hd : c.incoming <;> cases he : c.outgoing <;>
    simp [hd,he,Perpendicular,rightTurn,Direction.opposite] at hc <;>
    simp only [hd,he] at ho ⊢ <;> dsimp [Line.along,Direction.opposite] at ho ⊢ <;> unfold padding at * <;> omega

end PushPuzzle.PushS.FiniteRouting
