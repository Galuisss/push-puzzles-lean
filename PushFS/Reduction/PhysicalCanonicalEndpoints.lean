/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalSlots

/-! Exact actual gate boundary slots expressed in the neighboring source wire's phase convention. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles


open Cslib.Complexity.NCL Gadgets.Wires

theorem gate_canonical_endpoint (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (goal : Bool) {p r : GridRouting.Point} {d : Direction} (hn : neighbor d p=some r)
    {g : GateTileState} {a : Catalog.Bitmap.Args}
    (hg : key (CellPlan.cell (v,p))=some (.inl g)) (ha : key (CellPlan.cell (v,r))=some (.inr a))
    (i : Labels (.inl g)) (hf : GateTileRouting.FullGateBoundary.InFrame d
      ((slots goal (.inl g) i).1.val,(slots goal (.inl g) i).2.val)) :
    ∃inc prev : Bool,
      ((slots goal (.inl g) i).1.val,(slots goal (.inl g) i).2.val)=
        GateTileRouting.FullGateBoundary.endpointPoint d inc (if inc then !(wirePhase a goal) else wirePhase a goal) prev ∧
      (if inc then Catalog.targetDirection a.1=d.opposite else Catalog.sourceDirection a.1=d) := by
  obtain ⟨role,prev,hd,hpoint⟩ := gate_slots_frame g goal d i hf
  obtain ⟨b,hgc⟩ := gate_code hg
  obtain ⟨hgv,hgs⟩ := CellPlan.gate_sound hgc
  subst g
  obtain ⟨hmem,hbp⟩ := Raster.vertexAt_sound hgv
  obtain ⟨e,hac⟩ := wire_code ha
  have hd' : b.portDirection role=d := hd
  have hn' : neighbor (b.portDirection role) (refinePoint b.point)=some r := by rw [hd',hbp]; exact hn
  obtain ⟨hedge,hflow⟩ := CellPlan.gate_adjacent v hP hT hmem role hn' hac
  have hphase : gatePhase (gateTileState (b,v.2)) goal role=
      if (gateTileState (b,v.2)).incoming.get role then !(wirePhase a goal) else wirePhase a goal := by
    rw [gateTileState_incoming,wire_phase hac goal,←hedge]
    exact gate_phase v b goal role
  refine ⟨(gateTileState (b,v.2)).incoming.get role,prev,?_,?_⟩
  · rwa [hphase] at hpoint
  · rw [gateTileState_incoming,←hd']
    exact hflow

end PushPuzzle.PushFS.Reduction.PhysicalTiles
