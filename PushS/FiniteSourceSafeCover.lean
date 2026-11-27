/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceBoundaryOwners
public import PushS.FiniteRoutingLocalOwners

/-! Every active floor point of every actual global primitive chart has a real interior owner. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height InventoryAssembly.walls PrimitiveCode.instanceOf PrimitiveCode.chart
  Line.width Line.height Line.walls

-- Normalize dependent chart dimensions against the concrete flattened inventory.
set_option maxHeartbeats 1000000 in
/-- Complete actual safe-owner gluing, including cores, every tool and turn, and reciprocal source ports. -/
theorem chart_safe (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (c : Chart w v)
    (q : Cell (chart w hw v c).width (chart w hw v c).height)
    (hq : (chart w hw v c).classifier.name q ≠ .outside)
    (hf : (chart w hw v c).embedding.cells q ∉ (inventory w hw v).walls) :
    InteriorOwner w hw v ((chart w hw v c).embedding.cells q) ((chart w hw v c).classifier.name q).level := by
  have howner := FiniteSourceInventory.chart_owner_or_exit w hw v c q hq hf
  rcases howner with he | ho
  · rcases c with ⟨i,ch⟩
    let entry := (codes w v).get i
    change Cell (entry.2.chart w hw ch).width (entry.2.chart w hw ch).height at q
    change (entry.2.chart w hw ch).classifier.name q ≠ .outside at hq
    change entry.2.Exit w hw ((entry.2.chart w hw ch).embedding.cells q) at he
    have hmem : entry ∈ codes w v := List.get_mem _ _
    have hlocal := code_local w v entry hmem
    have hcoords : coordinates ((chart w hw v ⟨i,ch⟩).embedding.cells q) =
        macroShift w entry.1 (entry.2.world w hw ((entry.2.chart w hw ch).embedding.cells q)) := by
      have hp := (inventory w hw v).placedChart_cells i (entry.2.chart w hw ch) q
      exact (congrArg coordinates hp).trans (placed_wall_coordinates w hw v i _)
    have hstep := local_chart_exit_owner_or_port w hw (CellPlan.cell (v,entry.1)) entry.2 hlocal ch q hq he
    apply hstep.elim
    · intro ho
      exact worldOwner_lift w hw v entry.1 _ _ _ ho hcoords
    · intro hp
      obtain ⟨face,incoming,hport,hpoint,hlevel⟩ := hp
      change InteriorOwner w hw v ((chart w hw v ⟨i,ch⟩).embedding.cells q)
        ((entry.2.chart w hw ch).classifier.name q).level
      have hboundary := boundary_high_interior_owner w hw v hP hT entry.1 face incoming hport _
        (hcoords.trans (congrArg (macroShift w entry.1) hpoint))
      exact (congrArg (InteriorOwner w hw v ((chart w hw v ⟨i,ch⟩).embedding.cells q)) hlevel).mpr hboundary
  · exact ho

end PushPuzzle.PushS.FiniteSourceInventory
