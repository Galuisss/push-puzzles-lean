/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceEdgeReadout

/-! Actual unlabelled storage in the complete thick-wall compiler reflects original finite NCL reachability. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL PushPuzzle.NCL Plan PhysicalInventory
open PushFS.Gadgets.Wires.Soundness

attribute [local irreducible] codes width height Raster.width Raster.height InventoryAssembly.board InventoryAssembly.walls

variable (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)

private theorem sourceReadout_exclusive (hvalid : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (hG : (Word.compile v.1).graph.WellFormed)
    {S final : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)}
    (hs : Successful (slotMatching w hw v hP hT) S final) :
    PortClaims.Exclusive ((sourceReadout w hw v hvalid hP hT hG).read S) := by
  intro e both
  obtain ⟨i,hi⟩ := incidentPort_surjective hG (⟨e,false⟩ : Port (Fin (Word.compile v.1).edgeCount))
  obtain ⟨j,hj⟩ := incidentPort_surjective hG (⟨e,true⟩ : Port (Fin (Word.compile v.1).edgeCount))
  have hp := sourceRole_port v.1 hvalid hP hT i
  have hq := sourceRole_port v.1 hvalid hP hT j
  rw [hi] at hp
  rw [hj] at hq
  have hri := sourceReadout_incidence w hw v hvalid hP hT hG S i
  have hrj := sourceReadout_incidence w hw v hvalid hP hT hG S j
  rw [hi] at hri
  rw [hj] at hrj
  exact port_claims_exclusive hvalid hP hT hG e
    (sourceRecord v.1 hP hT i.1) (sourceRecord_mem v.1 hP hT i.1) (sourceRole v.1 hvalid hP hT i)
    (congrArg Port.edge hp) (congrArg Port.dir hp)
    (sourceRecord v.1 hP hT j.1) (sourceRecord_mem v.1 hP hT j.1) (sourceRole v.1 hvalid hP hT j)
    (congrArg Port.edge hq) (congrArg Port.dir hq) hs ⟨hri.symm.trans both.2,hrj.symm.trans both.1⟩

/-- The reverse proof uses the actual C1–C3 certificate, target identities, tool trajectories and finite source ports. -/
theorem ncl_of_solvable (hvalid : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (ha : (Word.compile v.1).checkLegal v.initialBits = true) (hb : (Word.compile v.1).checkLegal v.targetBits = true)
    {cap : Option ℕ} (hsol : (checkedPuzzle w hw v hP hT).Solvable cap) :
    (Word.compile v.1).graph.Reachable (fun e => v.initialBits.getD e.val false) (fun e => v.targetBits.getD e.val false) := by
  obtain ⟨t,hr,hsol⟩ := hsol
  obtain ⟨T,hTstate,hpath,hTpos⟩ := (ordered w hw v hP hT).lift_success (certificate w hw v hP hT) hr hsol
  have hgoals : T.state.boxes = (checkedPuzzle w hw v hP hT).board.goals := hTstate ▸ hsol
  exact (sourceReadout w hw v hvalid hP hT hvalid.2.2).successful_path hpath
    (fun S hbefore hafter => ⟨sourceReadout_exclusive w hw v hvalid hP hT hvalid.2.2 ⟨hbefore,hafter,hgoals⟩,
      sourceReadout_legal w hw v hvalid hP hT hvalid.2.2 ha hb ⟨hbefore,hafter,hgoals⟩⟩)
    (sourceReadout_initial w hw v hvalid hP hT hvalid.2.2) (sourceReadout_target w hw v hvalid hP hT hvalid.2.2 T hTpos)

end PushPuzzle.PushS.FiniteSourceInventory
