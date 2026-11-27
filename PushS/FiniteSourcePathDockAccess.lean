/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceTurnLaneLinks
public import PushS.FiniteSourceTerminalAccess

/-! Every actual line and turn dock on a routed gate arm or source wire has a real player-zero access walk. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.PathSite

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Line.width Line.height

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec} (s : PathSite w hw v P) (G : P.Geometry w)

private def lineDock (i : Fin P.segments.length) : Cell (width w v) (height w v) :=
  (s.line i).actualEmbedding.cells (Line.outerHub w (s.line i).atoms)

include G in
private theorem adjacent_line_docks_walk (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (i : Fin P.segments.length) (hi : i.val+1 < P.segments.length) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (s.lineDock i)) (PrimitiveProfile.state w hw v phase (s.lineDock ⟨i.val+1,hi⟩)) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (s.lineDock ⟨i.val+1,hi⟩)) (PrimitiveProfile.state w hw v phase (s.lineDock i)) := by
  by_cases ht : P.hasTurn i.val
  · exact s.turn_line_docks_walk G hP hT phase i ht
  · have H := P.collinear_contract w G i.val hi ht
    have hpos := (s.line_location i).trans (s.line_location ⟨i.val+1,hi⟩).symm
    exact (s.line i).normal_collinear_docks (s.line ⟨i.val+1,hi⟩) (admissible w hw v hP hT) phase H hpos

include G in
private theorem line_docks_walk (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (a b : Fin P.segments.length) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (s.lineDock a)) (PrimitiveProfile.state w hw v phase (s.lineDock b)) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (s.lineDock b)) (PrimitiveProfile.state w hw v phase (s.lineDock a)) := by
  have hlen : 0 < P.segments.length := by have h := a.isLt; omega
  let first : Fin P.segments.length := ⟨0,hlen⟩
  have hseq : ∀ n (hn : n < P.segments.length),
      Reachable (inventory w hw v).board (some 1)
        (PrimitiveProfile.state w hw v phase (s.lineDock first)) (PrimitiveProfile.state w hw v phase (s.lineDock ⟨n,hn⟩)) ∧
      Reachable (inventory w hw v).board (some 1)
        (PrimitiveProfile.state w hw v phase (s.lineDock ⟨n,hn⟩)) (PrimitiveProfile.state w hw v phase (s.lineDock first)) := by
    intro n
    induction n with
    | zero => intro hn; exact ⟨.refl,.refl⟩
    | succ n ih =>
      intro hn
      have hn' : n < P.segments.length := by omega
      have hp := ih hn'
      have hstep := s.adjacent_line_docks_walk G hP hT phase ⟨n,hn'⟩ hn
      exact ⟨hp.1.trans hstep.1,hstep.2.trans hp.2⟩
  have ha := hseq a.val a.isLt
  have hb := hseq b.val b.isLt
  exact ⟨ha.2.trans hb.1,hb.2.trans ha.1⟩

private def lastDockIndex (_s : PathSite w hw v P) (hlen : 0 < P.segments.length) : Fin P.segments.length := ⟨P.segments.length-1,by omega⟩

include G in
private theorem terminal_line_dock_access (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (hlen : 0 < P.segments.length) (face : Direction) (incoming : Bool)
    (hd : segmentDirection (P.line (P.segments.length-1)).segment = face)
    (he : (P.line (P.segments.length-1)).segment.finish = FiniteRouting.advance face.opposite (boundaryPoint w face) incoming.toNat)
    (i : Fin P.segments.length) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (inventory w hw v).player) (PrimitiveProfile.state w hw v phase (s.lineDock i)) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (s.lineDock i)) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) := by
  let last := s.lastDockIndex hlen
  have hend := (s.line last).normal_terminal_dock_access hP hT phase face incoming hd he
  have hwalk := s.line_docks_walk G hP hT phase last i
  exact ⟨hend.1.trans hwalk.1,hwalk.2.trans hend.2⟩

private theorem terminal_event_dock_access (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (hlen : 0 < P.segments.length) (face : Direction) (incoming : Bool)
    (hd : segmentDirection (P.line (P.segments.length-1)).segment = face)
    (he : (P.line (P.segments.length-1)).segment.finish = FiniteRouting.advance face.opposite (boundaryPoint w face) incoming.toNat)
    (a : PathEvent P) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (inventory w hw v).player) (PrimitiveProfile.state w hw v phase (s.eventDock G a)) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (s.eventDock G a)) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) := by
  cases a with
  | line i => exact s.terminal_line_dock_access G hP hT phase hlen face incoming hd he i
  | turn i hi =>
    have hline := s.terminal_line_dock_access G hP hT phase hlen face incoming hd he i
    have hturn := s.turn_dock_from_incoming G hP hT phase i hi
    exact ⟨hline.1.trans hturn.1,hturn.2.trans hline.2⟩

theorem arm_event_dock_access {g : GateTileState} {role : Fin 3} (p : PathSite w hw v (armSpec w g role))
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (phase : Fin (codes w v).length → Bool)
    (a : PathEvent (armSpec w g role)) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (inventory w hw v).player) (PrimitiveProfile.state w hw v phase (p.eventDock (armSpec_geometry w g role) a)) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (p.eventDock (armSpec_geometry w g role) a)) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) :=
  p.terminal_event_dock_access (armSpec_geometry w g role) hP hT phase (ArmBoundary.length_pos (w := w) (g := g) (role := role))
    (PortAnnulus.outerDirection (g.pattern,g.rotation,role)) (g.incoming.get role)
    (armSpec_last_direction w g role) (armSpec_last_finish w g role) a

theorem wire_event_dock_access {args : Gadgets.Wires.Catalog.Bitmap.Args} (p : PathSite w hw v (wireSpec w args))
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (phase : Fin (codes w v).length → Bool)
    (a : PathEvent (wireSpec w args)) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (inventory w hw v).player) (PrimitiveProfile.state w hw v phase (p.eventDock (wireSpec_geometry w args) a)) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (p.eventDock (wireSpec_geometry w args) a)) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) := by
  have hlen : 0 < (wireRoute w args.1).length := by rw [wireRoute_length]; split_ifs <;> decide
  have hlast : (wireRoute w args.1).length-1+1 = (wireRoute w args.1).length := by omega
  apply p.terminal_event_dock_access (wireSpec_geometry w args) hP hT phase hlen (Gadgets.Wires.Catalog.targetDirection args.1) false
    (wire_last_direction w args _ hlast) _ a
  change ((wireSpec w args).line ((wireRoute w args.1).length-1)).segment.finish =
    FiniteRouting.advance (Gadgets.Wires.Catalog.targetDirection args.1).opposite (boundaryPoint w (Gadgets.Wires.Catalog.targetDirection args.1)) 0
  simpa only [advance_zero] using wire_last_finish w args _ hlast

end PushPuzzle.PushS.FiniteSourceInventory.PathSite
