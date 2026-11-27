/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceWallMembership

public import PushS.FiniteRoutingTurnActionLocal
public import PushS.FiniteSourceTurnConnectivity

/-! Every literal four-box turn action is floor on the complete emitted source board. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem primitive_turn_action_wall_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point) (t : TurnCode) (ht : (pos,.turn t) ∈ codes w v)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.turnActive w)
    (other : GridRouting.Point) (d : PrimitiveCode) (hd : (other,d) ∈ codes w v)
    (q : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height) (hq : q ∈ (d.instanceOf w hw).board.walls) :
    macroShift w pos (t.actionWorld w hw p) ≠ macroShift w other (d.world w hw q) := by
  have htl := code_local w v (pos,.turn t) ht
  have hdl := code_local w v (other,d) hd
  let a := (Turn.orientation w t.incoming t.outgoing).cells p
  apply macro_actor_wall_ne w pos other _ _
    (local_world_bounds w hw (.turn t) (localCodes_fits w hw _ htl) a)
    (local_world_bounds w hw d (localCodes_fits w hw _ hdl) q)
    (by
      intro face hf
      exact ((interior_not_collar w face (local_turn_window_interior w hw _ t htl a)) hf).elim)
    (local_wall_collar_off_lane w hw _ d hdl q hq)
  intro hpos
  apply local_turn_action_ne_wall w hw (CellPlan.cell (v,pos)) t htl p hp d _ q hq
  simpa only [hpos] using hdl

namespace TurnSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : TurnSite w hw v)

theorem action_floor (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.turnActive w) :
    s.actualEmbedding.cells p ∉ (inventory w hw v).walls := by
  apply floor_of_wall_coordinates w hw v
  intro j q hq
  rw [s.actual_cell_coordinates]
  exact primitive_turn_action_wall_ne w hw v _ s.code s.code_mem p hp _ _ (List.get_mem _ _) q hq

end TurnSite
end PushPuzzle.PushS.FiniteSourceInventory
