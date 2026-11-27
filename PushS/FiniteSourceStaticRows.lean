/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingGateRows
public import PushS.FiniteSourceFloor

/-! Full working rows, including unowned slots, are floor in the emitted board. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem primitive_row_wall_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point) (c : LineCode) (hc : (pos,PrimitiveCode.line c) ∈ codes w v)
    (hgood : LineGood w c.segment) (n : ℕ) (hn : n ≤ segmentLength c.segment+1)
    (t : GridRouting.Point × PrimitiveCode) (ht : t ∈ codes w v)
    (p : Cell (t.2.instanceOf w hw).width (t.2.instanceOf w hw).height)
    (hp : p ∈ (t.2.instanceOf w hw).board.walls) :
    macroShift w pos (c.rowWorld w hw hgood n hn) ≠ macroShift w t.1 (t.2.world w hw p) := by
  have hcl := code_local w v (pos,.line c) hc
  have htl := code_local w v t ht
  apply macro_actor_wall_ne w pos t.1 _ _
    (local_world_bounds w hw (.line c) (localCodes_fits w hw _ hcl) (c.rowSlot w hw hgood n hn))
    (local_world_bounds w hw t.2 (localCodes_fits w hw _ htl) p)
    (local_row_collar_lane w hw _ c hcl hgood n hn)
    (local_wall_collar_off_lane w hw _ t.2 htl p hp)
  intro hpos
  apply local_row_wall_clear w hw (CellPlan.cell (v,pos)) c hcl hgood n hn t.2 _ p hp
  simpa only [hpos] using htl

theorem row_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point) (c : LineCode) (hc : (pos,PrimitiveCode.line c) ∈ codes w v)
    (hgood : LineGood w c.segment) (n : ℕ) (hn : n ≤ segmentLength c.segment+1)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos (c.rowWorld w hw hgood n hn)) :
    q ∉ (inventory w hw v).walls := by
  intro hm
  obtain ⟨j,_,hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨p,hp,he⟩ := Finset.mem_map.mp hm
  have he' := congrArg coordinates he
  rw [placed_wall_coordinates,hq] at he'
  exact primitive_row_wall_ne w hw v pos c hc hgood n hn _ (List.get_mem _ _) p hp he'.symm

end PushPuzzle.PushS.FiniteSourceInventory
