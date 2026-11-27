/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceEdgeGateForward

/-! Replay the actual complete compiler inventory along genuine NCL steps. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open Cslib.Complexity.NCL Plan SourceCanonical
open scoped Classical

attribute [local irreducible] codes Raster.width Raster.height inventory

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

/-- Literal narrow frames and real anchor walks for one complete actual ordinary path. -/
structure WireGeometry {a : Catalog.Bitmap.Args} (d : ℕ) (t : PathSite w hw v (wireSpec w a))
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (hc : CellPlan.cell (v,t.location) = some (.inr (d,a)))
    (phase : GridRouting.Point → Bool) (B : Board (width w v) (height w v)) : Prop where
  frames : ∀ cut,cut < PathSite.waveLength (P := wireSpec w a) → ∀ b : PathEvent (wireSpec w a),
    b.rank = PathSite.waveRank (P := wireSpec w a) cut →
    t.EventFrame (wireSpec_geometry w a) (actualWireInput hP hT d t hc).endpoints B (t.wave (tilePhases phase) cut) b
  access : t.WaveAccess (wireSpec_geometry w a) (tilePhases phase) B (inventory w hw v).player

/-- Literal selected core, full-arm frames and actual dock walks for one real gate update. -/
structure GateGeometry (c : CoreSite w hw v) (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role))
    (hloc : p.location = ((codes w v).get c.index).1) (g : VertexData)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (hc : CellPlan.cell (v,p.location) = some (.inl (g,c.gate)))
    (phase : GridRouting.Point → Bool) (B : Board (width w v) (height w v)) : Prop where
  core : c.Action (c.corePhase role p (tilePhases phase)) B
  core_access : c.AnchorAccess (c.corePhase role p (tilePhases phase)) B (inventory w hw v).player
  frames : ∀ cut,cut < PathSite.waveLength (P := armSpec w c.gate role) → ∀ a : PathEvent (armSpec w c.gate role),
    a.rank = PathSite.waveRank (P := armSpec w c.gate role) cut →
    p.EventFrame (armSpec_geometry w c.gate role) (actualArmInput hP hT c role p hloc g hc).endpoints B
      (p.wave (c.preparedArmBase role (tilePhases phase)) cut) a
  access : p.WaveAccess (armSpec_geometry w c.gate role) (c.preparedArmBase role (tilePhases phase)) B (inventory w hw v).player

/-- The finite geometric obligations for every actual tile reached by this one genuine source-edge frontier. -/
structure EdgeGeometry (w : ℕ) (hw : 2 ≤ w) (word : Word)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (f : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount) (target : List Bool) : Prop where
  wire : ∀ (d : ℕ) (a : Catalog.Bitmap.Args)
    (t : PathSite w hw (oneEdgeSource word f e) (wireSpec w a))
    (hc : CellPlan.cell (oneEdgeSource word f e,t.location) = some (.inr (d,a)))
    (phase : GridRouting.Point → Bool),TileFrontier word f e phase t.location →
    WireGeometry d t hP hT hc phase (canonicalBoard w hw word target)
  gate : ∀ (c : CoreSite w hw (oneEdgeSource word f e)) (role : Fin 3)
    (p : PathSite w hw (oneEdgeSource word f e) (armSpec w c.gate role))
    (hloc : p.location = ((codes w (oneEdgeSource word f e)).get c.index).1)
    (g : VertexData) (hc : CellPlan.cell (oneEdgeSource word f e,p.location) = some (.inl (g,c.gate))),
    (g.ports.port role).edge = e.val → ∀ phase,TileFrontier word f e phase p.location →
    GateGeometry c role p hloc g hP hT hc phase (canonicalBoard w hw word target)

private theorem unused_gate_update (w : ℕ) (hw : 2 ≤ w) (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (f : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (phase : GridRouting.Point → Bool) (pos : GridRouting.Point) (g : CellPlan.Gate)
    (hc : CellPlan.cell (oneEdgeSource word f e,pos) = some (.inl g))
    (hrole : ¬∃ role : Fin 3,(g.1.ports.port role).edge = e.val) :
    profileState w hw (oneEdgeSource word f e) phase =
      profileState w hw (oneEdgeSource word f e) (Function.update phase pos true) := by
  apply PrimitiveProfile.tile_update_idle
  obtain ⟨hv,hgate⟩ := CellPlan.gate_sound hc
  obtain ⟨hg,_⟩ := Raster.vertexAt_sound hv
  have hflags : g.2.core.initial = g.2.core.target := by
    rw [hgate]
    exact gate_unchanged word hG hP hT f e g.1 hg (by simpa only [not_exists] using hrole)
  intro code hm
  rw [hc] at hm
  exact gateCodes_samePhase w g.2 hflags hm

/-- Dispatch an actual source tile to its complete physical wire/gate program, marking idle tiles by equality. -/
private theorem edge_tile_forward (w : ℕ) (hw : 2 ≤ w) (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (f : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount) (target : List Bool)
    (G : EdgeGeometry w hw word hP hT f e target)
    (phase : GridRouting.Point → Bool) (pos : GridRouting.Point) (H : TileFrontier word f e phase pos) :
    Reachable (canonicalBoard w hw word target) (some 1)
      (profileState w hw (oneEdgeSource word f e) phase)
      (profileState w hw (oneEdgeSource word f e) (Function.update phase pos true)) := by
  let v := oneEdgeSource word f e
  have ha := admissible w hw v hP hT
  cases hc : CellPlan.cell (v,pos) with
  | none =>
    have he := PrimitiveProfile.tile_update_idle (w := w) (hw := hw) (v := v) phase pos (by
      intro code hm
      simp only [hc,localCodes,Option.elim_none,List.not_mem_nil] at hm)
    rw [←he]
    exact .refl
  | some code =>
    cases code with
    | inr a =>
      let t := PathSite.wire (hw := hw) pos a (record_mem pos (.inr a) hc)
      have geo := G.wire a.1 a.2 t hc phase H
      exact edge_wire_tile_forward w hw word hP hT f e ha a.1 t hc phase H _ geo.frames geo.access
    | inl g =>
      by_cases hrole : ∃ role : Fin 3,(g.1.ports.port role).edge = e.val
      · obtain ⟨role,he⟩ := hrole
        let c := CoreSite.of_gate (hw := hw) pos g (record_mem pos (.inl g) hc)
        let p := PathSite.arm (hw := hw) pos g role (record_mem pos (.inl g) hc)
        have hloc : p.location = ((codes w v).get c.index).1 := (CoreSite.of_gate_location pos g _).symm
        have geo := G.gate c role p hloc g.1 hc he phase H
        exact edge_gate_tile_forward w hw word hG hP hT f e ha c role p ⟨hloc,g.1,hc⟩ he phase H _
          geo.core geo.core_access geo.frames geo.access
      · rw [←unused_gate_update w hw word hG hP hT f e phase pos g hc hrole]
        exact .refl

/-- One genuine NCL edge reversal is a complete actual global single-box execution between canonical compiler states. -/
private theorem edge_forward (w : ℕ) (hw : 2 ≤ w) (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (f : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount) (target : List Bool)
    (G : EdgeGeometry w hw word hP hT f e target) :
    Reachable (canonicalBoard w hw word target) (some 1)
      (canonicalState w hw word target (configBits f))
      (canonicalState w hw word target (configBits (reverse f e))) :=
  edge_replay w hw word hG hP hT target f e (edge_tile_forward w hw word hG hP hT f e target G)

/-- Replay a legal NCL path using only the actual compiler's concrete wire and selected-core geometry. -/
private theorem ncl_forward (w : ℕ) (hw : 2 ≤ w) (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] []) (target : List Bool)
    (G : ∀ f e,word.compile.graph.Legal f → word.compile.graph.Legal (reverse f e) →
      EdgeGeometry w hw word hP hT f e target)
    {f g : Fin word.compile.edgeCount → Bool} (hr : word.compile.graph.Reachable f g) :
    Reachable (canonicalBoard w hw word target) (some 1)
      (canonicalState w hw word target (configBits f)) (canonicalState w hw word target (configBits g)) := by
  induction hr with
  | refl => exact .refl
  | @tail g h _ hs ih =>
    obtain ⟨hg,hh,e,rfl⟩ := hs
    exact ih.trans (edge_forward w hw word hG hP hT g e target (G g e hg hh))

/-- A genuine NCL path solves the actual full walled compiler puzzle by single-box pushes. -/
theorem checkedPuzzle_solvable_of_ncl (w : ℕ) (hw : 2 ≤ w) (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    {f g : Fin word.compile.edgeCount → Bool}
    (G : ∀ a e,word.compile.graph.Legal a → word.compile.graph.Legal (reverse a e) →
      EdgeGeometry w hw word hP hT a e (configBits g))
    (hr : word.compile.graph.Reachable f g) :
    (checkedPuzzle w hw (word,(configBits f,configBits g)) hP hT).Solvable (some 1) := by
  have hrun := ncl_forward w hw word hG hP hT (configBits g) G hr
  have hgoal := canonicalState_solved w hw word (configBits g)
  rw [canonicalBoard_eq w hw word (configBits g) (configBits f)] at hrun hgoal
  exact ⟨canonicalState w hw word (configBits g) (configBits g),hrun,hgoal⟩

end PushPuzzle.PushS.FiniteSourceInventory
