/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceTurnAccess
public import PushS.FiniteSourceNormalConnected
public import PushS.FiniteSourceLaneJunctions

/-! Actual neighboring line docks and the turn dock are joined at their literal open-quadrant lane intersection. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.PathSite

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Line.width Line.height FiniteTools.side

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec} (s : PathSite w hw v P) (G : P.Geometry w)

private theorem incoming_corner_walk (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (i : Fin P.segments.length) (hi : P.hasTurn i.val) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase ((s.line i).actualEmbedding.cells (Line.outerHub w (s.line i).atoms)))
      (PrimitiveProfile.state w hw v phase ((s.turn G i hi).actualEmbedding.cells (Turn.accessCorner w))) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase ((s.turn G i hi).actualEmbedding.cells (Turn.accessCorner w)))
      (PrimitiveProfile.state w hw v phase ((s.line i).actualEmbedding.cells (Line.outerHub w (s.line i).atoms))) := by
  have H := P.junction_contract w G i.val hi
  let q := turnIncomingCell w hw (P.line i.val) H.incoming_good (P.turn i.val) (Turn.accessCorner w) (Turn.accessCorner_mem w hw)
  have hb := turnIncomingCell_bounds w hw (P.line i.val) H.incoming_good (P.turn i.val) (Turn.accessCorner w) (Turn.accessCorner_mem w hw)
  have hlane : q = Line.outerCell w (s.line i).atoms (!(turnSide (P.turn i.val).incoming (P.turn i.val).outgoing)) q.1 :=
    turnIncomingCell_corner_lane w hw _ H.incoming_good _
  have he : (s.line i).actualEmbedding.cells q = (s.turn G i hi).actualEmbedding.cells (Turn.accessCorner w) :=
    s.turn_access_cell_eq G i hi _ (Turn.accessCorner_mem w hw)
  have hspan : Line.span w (s.line i).atoms = segmentLength (P.line i.val).segment := Line.program_span_of_bound w _ _ H.incoming_good.2.1
  have hpos : 1 ≤ Line.span w (s.line i).atoms := by have h := H.incoming_good.2.1; omega
  have hforward := (s.line i).normal_outer_connected hP hT phase true (!(turnSide (P.turn i.val).incoming (P.turn i.val).outgoing))
    (Line.outerHubX w (s.line i).atoms) q.1 (by dsimp [Line.outerHubX]; omega) (by dsimp [Line.outerHubX]; omega) hb.1 hb.2.1
  have hback := (s.line i).normal_outer_connected hP hT phase (!(turnSide (P.turn i.val).incoming (P.turn i.val).outgoing)) true
    q.1 (Line.outerHubX w (s.line i).atoms) hb.1 hb.2.1 (by dsimp [Line.outerHubX]; omega) (by dsimp [Line.outerHubX]; omega)
  rw [←hlane,he] at hforward hback
  exact ⟨hforward,hback⟩

private theorem outgoing_corner_cell (i : Fin P.segments.length) (hi : P.hasTurn i.val) :
    let j : Fin P.segments.length := ⟨i.val+1,hi.1⟩
    let x : Fin (Line.width w (s.line j).atoms) := ⟨FiniteTools.radius w+w,by
      have H := P.junction_contract w G i.val hi
      have hspan : Line.span w (s.line j).atoms = segmentLength (P.line (i.val+1)).segment := Line.program_span_of_bound w _ _ H.outgoing_good.2.1
      have hlen := H.outgoing_good.2.1
      unfold Line.width
      omega⟩
    (s.line j).actualEmbedding.cells (Line.outerCell w (s.line j).atoms (!(turnSide (P.turn i.val).incoming (P.turn i.val).outgoing)) x) =
      (s.turn G i hi).actualEmbedding.cells (Turn.accessCorner w) := by
  dsimp only
  have H := P.junction_contract w G i.val hi
  let j : Fin P.segments.length := ⟨i.val+1,hi.1⟩
  let c := P.line (i.val+1)
  let x : Fin (Line.width w (s.line j).atoms) := ⟨FiniteTools.radius w+w,by
    have hspan : Line.span w (s.line j).atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ H.outgoing_good.2.1
    have hlen := H.outgoing_good.2.1
    change 17*w+61 ≤ segmentLength c.segment at hlen
    unfold Line.width
    omega⟩
  let q := Line.outerCell w (s.line j).atoms (!(turnSide (P.turn i.val).incoming (P.turn i.val).outgoing)) x
  have hl := (s.line j).actual_cell_coordinates q
  have hr := (s.turn G i hi).actual_cell_coordinates (Turn.accessCorner w)
  rw [s.line_location] at hl
  rw [s.turn_location G i hi] at hr
  change coordinates ((s.line j).actualEmbedding.cells q) = macroShift w s.location
    (c.laneWorld w hw H.outgoing_good (!(turnSide (P.turn i.val).incoming (P.turn i.val).outgoing)) w (by
      have h : 17*w+61 ≤ segmentLength c.segment := H.outgoing_good.2.1
      omega)) at hl
  have hworld := turnOutgoingCorner_world w hw c H.outgoing_good (P.turn i.val) H.perpendicular H.outgoing_direction H.outgoing_start
  have he : coordinates ((s.line j).actualEmbedding.cells q) = coordinates ((s.turn G i hi).actualEmbedding.cells (Turn.accessCorner w)) :=
    hl.trans ((congrArg (macroShift w s.location) hworld).trans hr.symm)
  exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

private theorem outgoing_corner_walk (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (i : Fin P.segments.length) (hi : P.hasTurn i.val) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase ((s.line ⟨i.val+1,hi.1⟩).actualEmbedding.cells (Line.outerHub w (s.line ⟨i.val+1,hi.1⟩).atoms)))
      (PrimitiveProfile.state w hw v phase ((s.turn G i hi).actualEmbedding.cells (Turn.accessCorner w))) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase ((s.turn G i hi).actualEmbedding.cells (Turn.accessCorner w)))
      (PrimitiveProfile.state w hw v phase ((s.line ⟨i.val+1,hi.1⟩).actualEmbedding.cells (Line.outerHub w (s.line ⟨i.val+1,hi.1⟩).atoms))) := by
  let j : Fin P.segments.length := ⟨i.val+1,hi.1⟩
  have H := P.junction_contract w G i.val hi
  have hspan : Line.span w (s.line j).atoms = segmentLength (P.line (i.val+1)).segment := Line.program_span_of_bound w _ _ H.outgoing_good.2.1
  have hlen := H.outgoing_good.2.1
  let x : Fin (Line.width w (s.line j).atoms) := ⟨FiniteTools.radius w+w,by unfold Line.width; omega⟩
  have he := s.outgoing_corner_cell G i hi
  change (s.line j).actualEmbedding.cells (Line.outerCell w (s.line j).atoms (!(turnSide (P.turn i.val).incoming (P.turn i.val).outgoing)) x) = _ at he
  have hforward := (s.line j).normal_outer_connected hP hT phase true (!(turnSide (P.turn i.val).incoming (P.turn i.val).outgoing))
    (Line.outerHubX w (s.line j).atoms) x (by dsimp [Line.outerHubX]; omega) (by dsimp [Line.outerHubX]; omega)
    (by dsimp [x]; omega) (by dsimp [x]; omega)
  have hback := (s.line j).normal_outer_connected hP hT phase (!(turnSide (P.turn i.val).incoming (P.turn i.val).outgoing)) true
    x (Line.outerHubX w (s.line j).atoms) (by dsimp [x]; omega) (by dsimp [x]; omega)
    (by dsimp [Line.outerHubX]; omega) (by dsimp [Line.outerHubX]; omega)
  rw [he] at hforward hback
  exact ⟨hforward,hback⟩

include G in
theorem turn_line_docks_walk (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (i : Fin P.segments.length) (hi : P.hasTurn i.val) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase ((s.line i).actualEmbedding.cells (Line.outerHub w (s.line i).atoms)))
      (PrimitiveProfile.state w hw v phase ((s.line ⟨i.val+1,hi.1⟩).actualEmbedding.cells (Line.outerHub w (s.line ⟨i.val+1,hi.1⟩).atoms))) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase ((s.line ⟨i.val+1,hi.1⟩).actualEmbedding.cells (Line.outerHub w (s.line ⟨i.val+1,hi.1⟩).atoms)))
      (PrimitiveProfile.state w hw v phase ((s.line i).actualEmbedding.cells (Line.outerHub w (s.line i).atoms))) := by
  have ha := s.incoming_corner_walk G hP hT phase i hi
  have hb := s.outgoing_corner_walk G hP hT phase i hi
  exact ⟨ha.1.trans hb.2,hb.1.trans ha.2⟩

theorem turn_dock_from_incoming (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (i : Fin P.segments.length) (hi : P.hasTurn i.val) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase ((s.line i).actualEmbedding.cells (Line.outerHub w (s.line i).atoms)))
      (PrimitiveProfile.state w hw v phase ((s.turn G i hi).actualEmbedding.cells (FiniteTools.turnDock w))) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase ((s.turn G i hi).actualEmbedding.cells (FiniteTools.turnDock w)))
      (PrimitiveProfile.state w hw v phase ((s.line i).actualEmbedding.cells (Line.outerHub w (s.line i).atoms))) := by
  have ha := s.incoming_corner_walk G hP hT phase i hi
  have hb := s.turn_corner_dock_access G hP hT phase i hi
  exact ⟨ha.1.trans hb.1,hb.2.trans ha.2⟩

end PushPuzzle.PushS.FiniteSourceInventory.PathSite
