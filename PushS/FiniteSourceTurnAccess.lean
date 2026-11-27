/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingTurnAccess
public import PushS.FiniteSourceSideStock
public import PushS.FiniteSourceTurnConnectivity
public import PushS.FiniteSourcePathSites
public import PushS.FiniteSourceActionFloor
public import PushS.FiniteSourceLegal

/-! The actual turn access rectangle is an empty exposed piece of its actual incoming line for every normal global profile. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.PathSite

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Line.width Line.height FiniteTools.side

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec} (s : PathSite w hw v P) (G : P.Geometry w)

theorem turn_access_cell_eq (i : Fin P.segments.length) (hi : P.hasTurn i.val)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ Turn.accessRegion w) :
    (s.line i).actualEmbedding.cells (turnIncomingCell w hw (P.line i.val) (P.line_good w G i.val i.isLt) (P.turn i.val) p hp) =
      (s.turn G i hi).actualEmbedding.cells p := by
  let q := turnIncomingCell w hw (P.line i.val) (P.line_good w G i.val i.isLt) (P.turn i.val) p hp
  have hl := (s.line i).actual_cell_coordinates q
  have hr := (s.turn G i hi).actual_cell_coordinates p
  rw [s.line_location] at hl
  rw [s.turn_location G i hi] at hr
  change coordinates ((s.line i).actualEmbedding.cells q) = macroShift w s.location ((P.line i.val).actionWorld w hw q) at hl
  have H := P.junction_contract w G i.val hi
  have he := turnIncomingCell_world w hw (P.line i.val) H.incoming_good (P.turn i.val)
    H.incoming_direction H.incoming_finish p hp
  have he' : coordinates ((s.line i).actualEmbedding.cells q) = coordinates ((s.turn G i hi).actualEmbedding.cells p) :=
    hl.trans ((congrArg (macroShift w s.location) he).trans hr.symm)
  exact Prod.ext (Fin.ext (congrArg Prod.fst he')) (Fin.ext (congrArg Prod.snd he'))

private theorem turn_access_empty (phase : Fin (codes w v).length → Bool) (i : Fin P.segments.length) (hi : P.hasTurn i.val)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ Turn.accessRegion w) :
    (s.turn G i hi).actualEmbedding.cells p ∉ PrimitiveProfile.boxes w hw v phase := by
  rw [←s.turn_access_cell_eq G i hi p hp]
  have hb := turnIncomingCell_bounds w hw (P.line i.val) (P.line_good w G i.val i.isLt) (P.turn i.val) p hp
  exact (s.line i).normal_side_empty phase _ hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2

private theorem turn_access_free (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (i : Fin P.segments.length) (hi : P.hasTurn i.val)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ Turn.accessRegion w) :
    Free (inventory w hw v).board (PrimitiveProfile.boxes w hw v phase) ((s.turn G i hi).actualEmbedding.cells p) := by
  refine ⟨?_,s.turn_access_empty G phase i hi p hp⟩
  rw [←s.turn_access_cell_eq G i hi p hp]
  exact (s.line i).action_floor hP hT _
    (turnIncomingCell_active w hw (P.line i.val) (P.line_good w G i.val i.isLt) (P.turn i.val)
      (P.incoming_side i.val hi) p hp)

private theorem turn_access_walk (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (i : Fin P.segments.length) (hi : P.hasTurn i.val)
    (p q : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ Turn.accessRegion w) (hq : q ∈ Turn.accessRegion w) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase ((s.turn G i hi).actualEmbedding.cells p))
      (PrimitiveProfile.state w hw v phase ((s.turn G i hi).actualEmbedding.cells q)) := by
  have hfree (r : Cell (FiniteTools.side w) (FiniteTools.side w)) (hr : r ∈ FiniteAtomFrames.walkActive p q) :
      Free (inventory w hw v).board (PrimitiveProfile.boxes w hw v phase) ((s.turn G i hi).actualEmbedding.cells r) := by
    have hb := (FiniteAtomFrames.mem_walkActive p q r).mp hr
    have hp' := (Turn.mem_accessRegion w p).mp hp
    have hq' := (Turn.mem_accessRegion w q).mp hq
    apply s.turn_access_free G hP hT phase i hi r
    rw [Turn.mem_accessRegion]
    omega
  exact FiniteAtomFrames.walk_ambient p q (s.turn G i hi).actualEmbedding
    ⟨fun r hr => (hfree r hr).1,fun r hr => (hfree r hr).2,
      PrimitiveProfile.floor (admissible w hw v hP hT) phase⟩

theorem turn_corner_dock_access (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (i : Fin P.segments.length) (hi : P.hasTurn i.val) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase ((s.turn G i hi).actualEmbedding.cells (Turn.accessCorner w)))
      (PrimitiveProfile.state w hw v phase ((s.turn G i hi).actualEmbedding.cells (FiniteTools.turnDock w))) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase ((s.turn G i hi).actualEmbedding.cells (FiniteTools.turnDock w)))
      (PrimitiveProfile.state w hw v phase ((s.turn G i hi).actualEmbedding.cells (Turn.accessCorner w))) :=
  ⟨s.turn_access_walk G hP hT phase i hi _ _ (Turn.accessCorner_mem w hw) (Turn.dock_mem w hw),
    s.turn_access_walk G hP hT phase i hi _ _ (Turn.dock_mem w hw) (Turn.accessCorner_mem w hw)⟩

end PushPuzzle.PushS.FiniteSourceInventory.PathSite
