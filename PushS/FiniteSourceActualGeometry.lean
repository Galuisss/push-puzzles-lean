/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceForwardAccess
public import PushS.FiniteSourcePathLineFrames
public import PushS.FiniteSourcePathTurnFrames
public import PushS.FiniteSourceGateAction

/-! Complete actual wire and selected-core geometry for every genuine legal NCL reversal. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open Cslib.Complexity.NCL Plan SourceCanonical

attribute [local irreducible] codes Raster.width Raster.height inventory

variable {w : ℕ} {hw : 2 ≤ w} {word : Word}
  {f : Fin word.compile.edgeCount → Bool} {e : Fin word.compile.edgeCount}

private theorem wireGeometry_of_turnFrames (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (target : List Bool) {a : Catalog.Bitmap.Args} (d : ℕ)
    (t : PathSite w hw (oneEdgeSource word f e) (wireSpec w a))
    (hc : CellPlan.cell (oneEdgeSource word f e,t.location) = some (.inr (d,a)))
    (phase : GridRouting.Point → Bool) (H : TileFrontier word f e phase t.location)
    (F : ∀ cut,cut < PathSite.waveLength (P := wireSpec w a) →
      ∀ (i : Fin (wireSpec w a).segments.length) (hi : (wireSpec w a).hasTurn i.val),
      (PathEvent.turn i hi).rank = PathSite.waveRank (P := wireSpec w a) cut →
      t.EventFrame (wireSpec_geometry w a) (actualWireInput hP hT d t hc).endpoints
        (canonicalBoard w hw word target) (t.wave (tilePhases phase) cut) (.turn i hi)) :
    WireGeometry d t hP hT hc phase (canonicalBoard w hw word target) := by
  refine ⟨?_,t.canonical_wire_waveAccess hP hT target _⟩
  intro cut hcut b hrank
  cases b with
  | line i =>
    exact wire_line_event_frame hP hT d t hc phase H cut hcut i hrank _
      (canonical_walls w hw word (configBits f) (configBits (reverse f e)) target)
  | turn i hi => exact F cut hcut i hi hrank

private theorem gateGeometry_of_core_turnFrames (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] []) (target : List Bool)
    (c : CoreSite w hw (oneEdgeSource word f e)) (role : Fin 3)
    (p : PathSite w hw (oneEdgeSource word f e) (armSpec w c.gate role))
    (R : GateArmRecord c role p) (he : (R.vertex.ports.port role).edge = e.val)
    (phase : GridRouting.Point → Bool) (H : TileFrontier word f e phase p.location)
    (S : c.Action (c.corePhase role p (tilePhases phase)) (canonicalBoard w hw word target))
    (F : ∀ cut,cut < PathSite.waveLength (P := armSpec w c.gate role) →
      ∀ (i : Fin (armSpec w c.gate role).segments.length) (hi : (armSpec w c.gate role).hasTurn i.val),
      (PathEvent.turn i hi).rank = PathSite.waveRank (P := armSpec w c.gate role) cut →
      p.EventFrame (armSpec_geometry w c.gate role) (actualArmInput hP hT c role p R.location R.vertex R.cell).endpoints
        (canonicalBoard w hw word target) (p.wave (c.preparedArmBase role (tilePhases phase)) cut) (.turn i hi)) :
    GateGeometry c role p R.location R.vertex hP hT R.cell phase (canonicalBoard w hw word target) := by
  refine ⟨S,c.canonical_anchorAccess hP hT target _,?_,p.canonical_arm_waveAccess hP hT target _⟩
  intro cut hcut a hrank
  cases a with
  | line i =>
    exact arm_line_event_frame hG hP hT c role p R he phase H cut hcut i hrank _
      (canonical_walls w hw word (configBits f) (configBits (reverse f e)) target)
  | turn i hi => exact F cut hcut i hi hrank

private theorem actualWireGeometry (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (target : List Bool) {a : Catalog.Bitmap.Args} (d : ℕ)
    (t : PathSite w hw (oneEdgeSource word f e) (wireSpec w a))
    (hc : CellPlan.cell (oneEdgeSource word f e,t.location) = some (.inr (d,a)))
    (phase : GridRouting.Point → Bool) (H : TileFrontier word f e phase t.location) :
    WireGeometry d t hP hT hc phase (canonicalBoard w hw word target) := by
  obtain ⟨_,_,hinit,htarget⟩ := wire_reversed_phases word hP hT f e t.location d a hc H.point
  have hb : (wireSpec w a).target = !(wireSpec w a).initial := by
    change a.2.2 = !a.2.1
    rw [hinit,htarget,Bool.not_not]
  apply wireGeometry_of_turnFrames hP hT target d t hc phase H
  intro cut _ i hi _
  exact t.turn_event_frame (wireSpec_geometry w a) _ hb hP hT _ i hi _
    (canonical_walls w hw word (configBits f) (configBits (reverse f e)) target)

private theorem actual_gate_conditions (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (hf : word.compile.graph.Legal f) (hfe : word.compile.graph.Legal (reverse f e))
    (c : CoreSite w hw (oneEdgeSource word f e)) (role : Fin 3)
    (p : PathSite w hw (oneEdgeSource word f e) (armSpec w c.gate role))
    (R : GateArmRecord c role p) (he : (R.vertex.ports.port role).edge = e.val) :
    Gadgets.Gates.legal c.gate.core.isAND c.gate.core.initial ∧
    Gadgets.Gates.legal c.gate.core.isAND c.gate.core.target ∧
    Gadgets.Gates.singleChange c.gate.core.initial c.gate.core.target ∧
    (armSpec w c.gate role).target = !(armSpec w c.gate role).initial := by
  obtain ⟨hg,hgate⟩ := R.source_metadata
  refine ⟨?_,?_,?_,?_⟩
  · rw [hgate]
    exact gate_legal word hG hP hT f hf R.vertex hg
  · rw [hgate]
    exact gate_legal word hG hP hT (reverse f e) hfe R.vertex hg
  · rw [hgate]
    exact gate_singleChange word hG hP hT f e R.vertex hg role he
  · rw [hgate]
    exact (gate_reversed_phases w word hG hP hT f e R.vertex hg role he).2

private theorem actualGateGeometry (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (hf : word.compile.graph.Legal f) (hfe : word.compile.graph.Legal (reverse f e)) (target : List Bool)
    (c : CoreSite w hw (oneEdgeSource word f e)) (role : Fin 3)
    (p : PathSite w hw (oneEdgeSource word f e) (armSpec w c.gate role))
    (R : GateArmRecord c role p) (he : (R.vertex.ports.port role).edge = e.val)
    (phase : GridRouting.Point → Bool) (H : TileFrontier word f e phase p.location) :
    GateGeometry c role p R.location R.vertex hP hT R.cell phase (canonicalBoard w hw word target) := by
  obtain ⟨hi,hf',hs,hb⟩ := actual_gate_conditions hG hP hT hf hfe c role p R he
  have hB := canonical_walls w hw word (configBits f) (configBits (reverse f e)) target
  apply gateGeometry_of_core_turnFrames hG hP hT target c role p R he phase H
    (c.actual_action role p R.location hP hT (admissible w hw _ hP hT) R.vertex R.cell phase H.fresh hb _ hB hi hf' hs)
  intro cut _ i hi _
  exact p.turn_event_frame (armSpec_geometry w c.gate role) _ hb hP hT _ i hi _ hB

/-- Every instruction and anchor walk of a genuine legal NCL reversal uses the actual emitted full board. -/
theorem actualEdgeGeometry (w : ℕ) (hw : 2 ≤ w) (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (f : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount) (target : List Bool)
    (hf : word.compile.graph.Legal f) (hfe : word.compile.graph.Legal (reverse f e)) :
    EdgeGeometry w hw word hP hT f e target := by
  constructor
  · intro d a t hc phase H
    exact actualWireGeometry hP hT target d t hc phase H
  · intro c role p hloc vertex hc he phase H
    exact actualGateGeometry hG hP hT hf hfe target c role p ⟨hloc,vertex,hc⟩ he phase H

end PushPuzzle.PushS.FiniteSourceInventory
