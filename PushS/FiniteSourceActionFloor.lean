/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceWallMembership

public import PushS.FiniteRoutingActionContacts
public import PushS.FiniteSourceTravelHulls
public import PushS.FiniteSourceLineConnectivity

/-! Every strict line action footprint is floor on the actual complete emitted source board. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem primitive_action_wall_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (pos : GridRouting.Point) (c : LineCode) (hc : (pos,.line c) ∈ codes w v)
    (p : c.ActionCell w)
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last)
    (other : GridRouting.Point) (d : PrimitiveCode) (hd : (other,d) ∈ codes w v)
    (q : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height) (hq : q ∈ (d.instanceOf w hw).board.walls) :
    macroShift w pos (c.actionWorld w hw p) ≠ macroShift w other (d.world w hw q) := by
  have hcl := code_local w v (pos,.line c) hc
  have hdl := code_local w v (other,d) hd
  have hgood := (local_line_good w _ c hcl).1
  intro heq
  by_cases hpos : pos = other
  · subst other
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    dsimp [macroShift] at hx hy
    exact local_action_ne_wall w hw (CellPlan.cell (v,pos)) c hcl p hp d hdl q hq (Prod.ext (by omega) (by omega))
  · obtain ⟨face,hn,hfa,hfb⟩ := macro_band_contact w (w+1) (by unfold padding; omega) pos other
      (c.actionWorld w hw p) (d.world w hw q)
      (local_world_bounds w hw (.line c) (localCodes_fits w hw _ hcl)
        ((Line.rotation w _ (segmentDirection c.segment)).cells p))
      (local_world_bounds w hw d (localCodes_fits w hw _ hdl) q)
      (by
        intro face hf
        obtain ⟨incoming,_,hport⟩ := local_action_collar_port w hw _ c hcl p hp face hf
        exact hport.action_band w hw c hgood face incoming p hp) hpos heq
    obtain ⟨incoming,hport,hcp⟩ := local_action_collar_port w hw _ c hcl p hp face hfa
    obtain ⟨e,out,rfl,heport,hep⟩ := local_wall_collar_line_port w hw _ d hdl q hq face.opposite hfb
    have hrec := local_port_reciprocal v hP hT pos other face hn incoming hport
    have hout := local_port_unique (CellPlan.cell (v,other)) face.opposite out (!incoming) heport hrec
    rw [hout] at hep
    exact port_action_ne_wall w hw pos other face hn incoming c e hgood
      (local_line_good w _ e hdl).1 hcp hep p hp q hq heq

namespace LineSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

theorem action_floor (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p : Cell (Line.width w s.atoms) (Line.height w))
    (hp : p ∈ Line.Action.active w s.atoms s.code.above s.code.last) :
    s.actualEmbedding.cells p ∉ (inventory w hw v).walls := by
  apply floor_of_wall_coordinates w hw v
  intro j q hq
  rw [s.actual_cell_coordinates]
  exact primitive_action_wall_ne w hw v hP hT _ s.code s.code_mem p hp _ _ (List.get_mem _ _) q hq

end LineSite
end PushPuzzle.PushS.FiniteSourceInventory
