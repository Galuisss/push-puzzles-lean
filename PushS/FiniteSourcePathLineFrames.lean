/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceActionStock
public import PushS.FiniteSourceActionFloor
public import PushS.FiniteSourceTerminalWave

/-! Genuine source frontiers supply complete actual line event frames without geometric premises. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open Cslib.Complexity.NCL Plan SourceCanonical
open scoped Classical

attribute [local irreducible] codes width height Raster.width Raster.height

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec}

private theorem PathSite.line_event_frame (s : PathSite w hw v P) (G : P.Geometry w) (E : s.Endpoints)
    (hb : P.target = !P.initial) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (i : Fin P.segments.length)
    (F : PathEvent.Frontier s phase (.line i))
    (T : i.val+1 = P.segments.length → (s.line i).code.last = true → (s.line i).TerminalNeighbor phase)
    (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    s.EventFrame G E B phase (.line i) := by
  have ha := admissible w hw v hP hT
  refine ⟨?_,s.line_fixed_avoids G E ha hb hP hT phase i F T,?_⟩
  · intro p hp
    rw [hB]
    exact (s.line i).action_floor hP hT p hp
  · rw [hB]
    exact PrimitiveProfile.outside_floor ha phase _

variable {word : Word} {f : Fin word.compile.edgeCount → Bool} {e : Fin word.compile.edgeCount}

private def wire_terminal_neighbor (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    {a : Catalog.Bitmap.Args} (d : ℕ) (t : PathSite w hw (oneEdgeSource word f e) (wireSpec w a))
    (hc : CellPlan.cell (oneEdgeSource word f e,t.location) = some (.inr (d,a)))
    (phase : GridRouting.Point → Bool) (H : TileFrontier word f e phase t.location)
    (cut : ℕ) (i : Fin (wireSpec w a).segments.length) (hi : i.val+1 = (wireSpec w a).segments.length) :
    (t.line i).TerminalNeighbor (t.wave (tilePhases phase) cut) where
  face := Catalog.targetDirection a.1
  producer := wire_last_port w a i.val hi
  consumerLow j hn := wire_wave_consumer_low hP hT d t hc phase H cut j (by simpa only [t.line_location] using hn)

private def arm_terminal_neighbor (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (c : CoreSite w hw (oneEdgeSource word f e)) (role : Fin 3)
    (p : PathSite w hw (oneEdgeSource word f e) (armSpec w c.gate role))
    (R : GateArmRecord c role p) (he : (R.vertex.ports.port role).edge = e.val)
    (phase : GridRouting.Point → Bool) (H : TileFrontier word f e phase p.location)
    (cut : ℕ) (i : Fin (armSpec w c.gate role).segments.length)
    (hi : i.val+1 = (armSpec w c.gate role).segments.length) (hlast : (p.line i).code.last = true) :
    (p.line i).TerminalNeighbor (p.wave (c.preparedArmBase role (tilePhases phase)) cut) := by
  have hin : c.gate.incoming.get role = false := by
    simp only [PathSite.line,PathSpec.line,lineCodeAt,ownsLast,hi,ite_true] at hlast
    change (!(c.gate.incoming.get role)) = true at hlast
    cases hh : c.gate.incoming.get role <;> simp_all
  have hi' : i.val = (armRoute w c.gate role).length-1 := by
    change i.val+1 = (armRoute w c.gate role).length at hi
    omega
  refine ⟨PortAnnulus.outerDirection (c.gate.pattern,c.gate.rotation,role),?_,?_⟩
  · simpa only [PathSite.line,gatePortLine,←hi',hin] using gatePortLine_port w c.gate role
  · intro j hn
    exact arm_wave_consumer_low hP hT c role p R.location R.vertex R.cell he hin phase H cut j
      (by simpa only [p.line_location] using hn)

theorem wire_line_event_frame (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    {a : Catalog.Bitmap.Args} (d : ℕ) (t : PathSite w hw (oneEdgeSource word f e) (wireSpec w a))
    (hc : CellPlan.cell (oneEdgeSource word f e,t.location) = some (.inr (d,a)))
    (phase : GridRouting.Point → Bool) (H : TileFrontier word f e phase t.location)
    (cut : ℕ) (hcut : cut < PathSite.waveLength (P := wireSpec w a)) (i : Fin (wireSpec w a).segments.length)
    (hrank : (PathEvent.line i).rank = PathSite.waveRank (P := wireSpec w a) cut)
    (B : Board (width w (oneEdgeSource word f e)) (height w (oneEdgeSource word f e)))
    (hB : B.walls = (inventory w hw (oneEdgeSource word f e)).walls) :
    t.EventFrame (wireSpec_geometry w a) (actualWireInput hP hT d t hc).endpoints B (t.wave (tilePhases phase) cut) (.line i) := by
  obtain ⟨_,_,hi,ht⟩ := wire_reversed_phases word hP hT f e t.location d a hc H.point
  apply t.line_event_frame (wireSpec_geometry w a) _ (by
    change a.2.2 = !a.2.1
    rw [hi,ht,Bool.not_not]) hP hT _ i
    (t.wave_frontier (wireSpec_geometry w a) _ (t.path_fresh phase H.fresh) cut hcut _ hrank) _ B hB
  intro hlast _
  exact wire_terminal_neighbor hP hT d t hc phase H cut i hlast

theorem arm_line_event_frame (hG : word.compile.Valid) (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (c : CoreSite w hw (oneEdgeSource word f e)) (role : Fin 3)
    (p : PathSite w hw (oneEdgeSource word f e) (armSpec w c.gate role))
    (R : GateArmRecord c role p) (he : (R.vertex.ports.port role).edge = e.val)
    (phase : GridRouting.Point → Bool) (H : TileFrontier word f e phase p.location)
    (cut : ℕ) (hcut : cut < PathSite.waveLength (P := armSpec w c.gate role))
    (i : Fin (armSpec w c.gate role).segments.length)
    (hrank : (PathEvent.line i).rank = PathSite.waveRank (P := armSpec w c.gate role) cut)
    (B : Board (width w (oneEdgeSource word f e)) (height w (oneEdgeSource word f e)))
    (hB : B.walls = (inventory w hw (oneEdgeSource word f e)).walls) :
    p.EventFrame (armSpec_geometry w c.gate role) (actualArmInput hP hT c role p R.location R.vertex R.cell).endpoints B
      (p.wave (c.preparedArmBase role (tilePhases phase)) cut) (.line i) := by
  obtain ⟨hg,hgate⟩ := R.source_metadata
  have hb : (armSpec w c.gate role).target = !(armSpec w c.gate role).initial := by
    rw [hgate]
    exact (gate_reversed_phases w word hG hP hT f e R.vertex hg role he).2
  apply p.line_event_frame (armSpec_geometry w c.gate role) _ hb hP hT _ i
    (p.wave_frontier (armSpec_geometry w c.gate role) _ (c.preparedArmBase_fresh role p phase H.fresh)
      cut hcut _ hrank) _ B hB
  intro hlast howned
  exact arm_terminal_neighbor hP hT c role p R he phase H cut i hlast howned

end PushPuzzle.PushS.FiniteSourceInventory
