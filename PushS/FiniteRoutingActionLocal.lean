/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionCore
public import PushS.FiniteRoutingGateRows

/-! Every actual line action cell avoids the complete wall union of its emitted source tile. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

attribute [local irreducible] Line.width Line.height Line.walls Line.program Line.span FiniteTools.side FiniteGeometry.side

private theorem gate_action_ne_wall (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (c : LineCode) (hc : PrimitiveCode.line c ∈ gateCodes w g) (p : c.ActionCell w)
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last)
    (d : PrimitiveCode) (hd : d ∈ gateCodes w g)
    (q : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height) (hq : q ∈ (d.instanceOf w hw).board.walls) :
    c.actionWorld w hw p ≠ d.world w hw q := by
  obtain ⟨role,i,hi,rfl⟩ := gate_line_origin w g c hc
  rw [gateCodes_eq_specs] at hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact arm_action_ne_core_wall w hw g role i hi p hp q hq
  · obtain ⟨other,_,hd⟩ := List.mem_flatMap.mp hd
    by_cases hro : role = other
    · subst other
      exact (armSpec w g role).action_ne_codes_wall w hw (armSpec_geometry w g role) i hi p hp d hd q hq
    · exact different_arms_action_ne_wall w hw g role other hro i hi p hp d hd q hq

private theorem wire_action_ne_wall (w : ℕ) (hw : 2 ≤ w) (a : Catalog.Bitmap.Args)
    (c : LineCode) (hc : PrimitiveCode.line c ∈ wireCodes w a) (p : c.ActionCell w)
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last)
    (d : PrimitiveCode) (hd : d ∈ wireCodes w a)
    (q : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height) (hq : q ∈ (d.instanceOf w hw).board.walls) :
    c.actionWorld w hw p ≠ d.world w hw q := by
  obtain ⟨i,hi,rfl⟩ := (wireSpec w a).line_code_origin c hc
  exact (wireSpec w a).action_ne_codes_wall w hw (wireSpec_geometry w a) i hi p hp d hd q hq

theorem local_action_ne_wall (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code)
    (c : LineCode) (hc : PrimitiveCode.line c ∈ FiniteSourceInventory.localCodes w code) (p : c.ActionCell w)
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last)
    (d : PrimitiveCode) (hd : d ∈ FiniteSourceInventory.localCodes w code)
    (q : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height) (hq : q ∈ (d.instanceOf w hw).board.walls) :
    c.actionWorld w hw p ≠ d.world w hw q := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code =>
    cases code with
    | inl g => exact gate_action_ne_wall w hw g.2 c hc p hp d hd q hq
    | inr a => exact wire_action_ne_wall w hw a.2 c hc p hp d hd q hq

end PushPuzzle.PushS.FiniteRouting
