/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingSupportCaps
public import PushS.FiniteRoutingPathLayout

/-! Every scalar row cell, including unowned endpoints, has its actual line geometry. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side

namespace LineCode

def rowSlot (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (n : ℕ) (hn : n ≤ segmentLength c.segment+1) :
    Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height :=
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let q : Cell (Line.span w atoms+2) (Line.height w) :=
    (⟨n,by have h : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1; omega⟩,
      Line.railRow w)
  (Line.rotation w atoms (segmentDirection c.segment)).cells ((Line.railEmbedding w atoms).cells q)

def rowWorld (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (n : ℕ) (hn : n ≤ segmentLength c.segment+1) : ℕ × ℕ :=
  (PrimitiveCode.line c).world w hw (c.rowSlot w hw hc n hn)

theorem rowWorld_eq (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (n : ℕ) (hn : n ≤ segmentLength c.segment+1) :
    c.rowWorld w hw hc n hn = Line.along w (segmentDirection c.segment) c.segment.start n := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have hlen : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  let q : Cell (Line.span w atoms+2) (Line.height w) := (⟨n,by omega⟩,Line.railRow w)
  have ht := segment_travels c.segment hc.1
  have hr := Line.rotation_coordinates w atoms (segmentDirection c.segment) ((Line.railEmbedding w atoms).cells q)
  have hx := congrArg Prod.fst hr
  have hy := congrArg Prod.snd hr
  dsimp only at hx hy
  change (Line.offsetX w atoms (segmentDirection c.segment) c.segment.start+
      ((Line.rotation w atoms (segmentDirection c.segment)).cells ((Line.railEmbedding w atoms).cells q)).1.val,
    Line.offsetY w atoms (segmentDirection c.segment) c.segment.start+
      ((Line.rotation w atoms (segmentDirection c.segment)).cells ((Line.railEmbedding w atoms).cells q)).2.val) = _
  rw [hx,hy]
  clear hr hx hy
  cases hd : segmentDirection c.segment <;> simp only [hd] at ht ⊢ <;>
    dsimp [q,Line.rotatedCoordinates,Line.railEmbedding,GridEmbedding.translate,Line.railRow,
      Line.offsetX,Line.offsetY,Line.anchor,Travels,Line.along] at * <;> apply Prod.ext <;>
    simp only [Line.width,Line.height,FiniteTools.side,FiniteTools.radius,padding] at * <;> omega

theorem row_footprint (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (n : ℕ) (hn : n ≤ segmentLength c.segment+1) :
    ∃ u, c.segment.Contains u ∧ Nearby 1 (c.rowWorld w hw hc n hn) (padding w+u.1,padding w+u.2) := by
  let t := min n (segmentLength c.segment)
  have ht : t ≤ segmentLength c.segment := min_le_right _ _
  have htravel := segment_travels c.segment hc.1
  refine ⟨advance (segmentDirection c.segment) c.segment.start t,advance_contains _ _ _ _ t htravel ht,?_⟩
  rw [rowWorld_eq]
  cases hd : segmentDirection c.segment <;> simp only [hd] at htravel ⊢ <;>
    dsimp [t,Travels,Nearby,Line.along,advance] at * <;> unfold padding at * <;> omega

theorem row_ne_own_wall (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (n : ℕ) (hn : n ≤ segmentLength c.segment+1)
    (p : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) :
    c.rowWorld w hw hc n hn ≠ (PrimitiveCode.line c).world w hw p := by
  obtain ⟨_,_,hrow⟩ := line_wall_envelope w hw c hc p hp
  intro he
  rw [←he,rowWorld_eq] at hrow
  cases hd : segmentDirection c.segment <;> simp only [hd] at hrow <;> dsimp [SameLane,Line.along] at hrow <;> omega

theorem incoming_row_ray (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (hd : segmentDirection c.segment = t.incoming)
    (hf : c.segment.finish = advance t.incoming.opposite t.corner 2)
    (n : ℕ) (hn : n ≤ segmentLength c.segment+1) :
    c.rowWorld w hw hc n hn = Line.along w t.incoming.opposite t.corner (segmentLength c.segment+2-n) := by
  rw [rowWorld_eq,hd]
  have ht := segment_travels c.segment hc.1
  rw [hd,hf] at ht
  have hl := hc.2.1
  cases hdi : t.incoming <;> simp only [hdi] at ht ⊢ <;>
    dsimp [Travels,Line.along,advance,Direction.opposite] at ht ⊢ <;> apply Prod.ext <;>
    unfold padding <;> omega

theorem outgoing_row_ray (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (hd : segmentDirection c.segment = t.outgoing)
    (hs : c.segment.start = advance t.outgoing t.corner 1)
    (n : ℕ) (hn : n ≤ segmentLength c.segment+1) :
    c.rowWorld w hw hc n hn = Line.along w t.outgoing t.corner (n+1) := by
  rw [rowWorld_eq,hd,hs]
  have ht := segment_travels c.segment hc.1
  rw [hd,hs] at ht
  exact outgoing_along_ray w _ t.outgoing c.segment.finish t.corner ht (by have h := hc.2.1; omega) n hn

end LineCode

end PushPuzzle.PushS.FiniteRouting
