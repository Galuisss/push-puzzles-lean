/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePorts
public import PushS.FiniteRoutingBoundaryOwners
public import PushS.FiniteSourceOwners

/-! Every actual source boundary high exit is a real neighbor's low interior-owner slot. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

private theorem rail_name_opposite (w : ℕ) (d : Direction) :
    Line.orientedRailName w d.opposite = Line.orientedRailName w d := by cases d <;> rfl

private theorem neighbor_boundary_owner (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p : GridRouting.Point) (face : Direction) (incoming : Bool)
    (hp : LocalPort (CellPlan.cell (v,p)) face incoming) :
    ∃ r, PushFS.Reduction.neighbor face p = some r ∧
      LocalPort (CellPlan.cell (v,r)) face.opposite (!incoming) ∧
      WorldOwner w hw (localCodes w (CellPlan.cell (v,r)))
        (boundarySlot w face.opposite (!incoming) false) (Line.orientedRailName w face).level ∧
      macroShift w p (boundarySlot w face incoming true) =
        macroShift w r (boundarySlot w face.opposite (!incoming) false) := by
  obtain ⟨r,hn,_⟩ := CellPlan.used_neighbor v hP hT p face (local_port_used v p face incoming hp)
  have hport := local_port_reciprocal v hP hT p r face hn incoming hp
  have howner := local_port_low_owner w hw (CellPlan.cell (v,r)) face.opposite (!incoming) hport
  rw [rail_name_opposite] at howner
  exact ⟨r,hn,hport,howner,macro_boundary_seam w face p r incoming hn⟩

/-- The canonical high exit of every actual used source port has a real global interior owner. -/
theorem boundary_high_interior_owner (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p : GridRouting.Point) (face : Direction) (incoming : Bool)
    (hp : LocalPort (CellPlan.cell (v,p)) face incoming)
    (actual : Cell (width w v) (height w v))
    (hactual : coordinates actual = macroShift w p (boundarySlot w face incoming true)) :
    InteriorOwner w hw v actual (Line.orientedRailName w face).level := by
  obtain ⟨r,_,_,ho,he⟩ := neighbor_boundary_owner w hw v hP hT p face incoming hp
  exact worldOwner_lift w hw v r _ _ actual ho (hactual.trans he)

end PushPuzzle.PushS.FiniteSourceInventory
