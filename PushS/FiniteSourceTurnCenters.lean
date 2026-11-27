/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingTurnCenters
public import PushS.FiniteSourceFloor

/-! Every actual turn corner remains floor under the global primitive wall union. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem primitive_center_wall_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point) (c : TurnCode) (hc : (pos,PrimitiveCode.turn c) ∈ codes w v)
    (t : GridRouting.Point × PrimitiveCode) (ht : t ∈ codes w v)
    (p : Cell (t.2.instanceOf w hw).width (t.2.instanceOf w hw).height)
    (hp : p ∈ (t.2.instanceOf w hw).board.walls) :
    macroShift w pos (c.centerWorld w hw) ≠ macroShift w t.1 (t.2.world w hw p) := by
  have hcl := code_local w v (pos,.turn c) hc
  have htl := code_local w v t ht
  apply macro_actor_wall_ne w pos t.1 _ _
    (local_world_bounds w hw (.turn c) (localCodes_fits w hw _ hcl) (c.centerSlot w))
    (local_world_bounds w hw t.2 (localCodes_fits w hw _ htl) p)
    (fun face hf => ((interior_not_collar w face (local_turn_window_interior w hw _ c hcl (c.centerSlot w))) hf).elim)
    (local_wall_collar_off_lane w hw _ t.2 htl p hp)
  intro hpos
  apply local_center_wall_clear w hw (CellPlan.cell (v,pos)) c hcl t.2 _ p hp
  simpa only [hpos] using htl

theorem center_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point) (c : TurnCode) (hc : (pos,PrimitiveCode.turn c) ∈ codes w v)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos (c.centerWorld w hw)) :
    q ∉ (inventory w hw v).walls := by
  intro hm
  obtain ⟨j,_,hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨p,hp,he⟩ := Finset.mem_map.mp hm
  have he' := congrArg coordinates he
  rw [placed_wall_coordinates,hq] at he'
  exact primitive_center_wall_ne w hw v pos c hc _ (List.get_mem _ _) p hp he'.symm

end PushPuzzle.PushS.FiniteSourceInventory
