/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteCoreActiveFloor
public import PushS.FiniteSourceCoreConnectivity

/-! The whole actual source board preserves every selected-core envelope floor cell. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteCoreGuardCoverage FiniteGateActiveRegion
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height FiniteGeometry.side Line.width Line.height

private theorem core_envelope_local_clear (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (g : GateTileState)
    (hc : .core g ∈ localCodes w code)
    (a : Cell (FiniteGeometry.side w) (FiniteGeometry.side w))
    (henv : Envelope w g.core.isAND (coordinates a)) (hfloor : a ∉ FiniteCoreGuardCoverage.walls w g.core.isAND)
    (d : PrimitiveCode) (hd : d ∈ localCodes w code)
    (p : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height) (hp : p ∈ (d.instanceOf w hw).board.walls) :
    coreWorld w a ≠ d.world w hw p := by
  cases code with
  | none => simp [localCodes] at hc
  | some code =>
    cases code with
    | inl h =>
      have he := gate_core_origin w g h.2 hc
      subst g
      exact FiniteGateActiveRegion.core_gate_wall_clear w hw h.2 a henv hfloor d hd p hp
    | inr q => exact ((wireSpec w q.2).core_not_mem g hc).elim

/-- Every source primitive wall avoids the concrete envelope floor of an actual emitted core. -/
private theorem core_envelope_wall_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point) (g : GateTileState) (hc : (pos,PrimitiveCode.core g) ∈ codes w v)
    (a : Cell (FiniteGeometry.side w) (FiniteGeometry.side w))
    (henv : Envelope w g.core.isAND (coordinates a)) (hfloor : a ∉ FiniteCoreGuardCoverage.walls w g.core.isAND)
    (t : GridRouting.Point × PrimitiveCode) (ht : t ∈ codes w v)
    (p : Cell (t.2.instanceOf w hw).width (t.2.instanceOf w hw).height) (hp : p ∈ (t.2.instanceOf w hw).board.walls) :
    macroShift w pos (coreWorld w a) ≠ macroShift w t.1 (t.2.world w hw p) := by
  have hcl := code_local w v (pos,.core g) hc
  have htl := code_local w v t ht
  have hb := local_world_bounds w hw (.core g) (localCodes_fits w hw _ hcl) (coreCell w hw g a)
  rw [coreCell_world] at hb
  have hactor : ∀ face,InCollar w face (coreWorld w a) →
      SameLane face (Line.along w face (boundaryPoint w face) 0) (coreWorld w a) := by
    intro face hf
    have hh := core_window_interior w hw g (coreCell w hw g a)
    rw [coreCell_world] at hh
    exact ((interior_not_collar w face hh) hf).elim
  apply macro_actor_wall_ne w pos t.1 _ _ hb
    (local_world_bounds w hw t.2 (localCodes_fits w hw _ htl) p)
    hactor (local_wall_collar_off_lane w hw _ t.2 htl p hp)
  intro hpos
  apply core_envelope_local_clear w hw (CellPlan.cell (v,pos)) g hcl a henv hfloor t.2 _ p hp
  simpa only [hpos] using htl

namespace CoreSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (c : CoreSite w hw v)

/-- Every actual core-envelope floor cell is floor on the complete emitted source board. -/
theorem envelope_floor (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w))
    (henv : Envelope w c.gate.core.isAND (coordinates p))
    (hfloor : p ∉ FiniteCoreGuardCoverage.walls w c.gate.core.isAND) :
    c.embedding.cells p ∉ (inventory w hw v).walls := by
  intro hm
  obtain ⟨j,_,hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hm
  have hh := congrArg coordinates he
  rw [placed_wall_coordinates,c.embedding_coordinates] at hh
  exact core_envelope_wall_ne w hw v _ c.gate c.mem_codes p henv hfloor _ (List.get_mem _ _) q hq hh.symm

end CoreSite
end PushPuzzle.PushS.FiniteSourceInventory
