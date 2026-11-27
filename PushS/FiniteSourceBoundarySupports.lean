/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingBoundarySupports
public import PushS.FiniteSourceStaticRows
public import PushS.FiniteSourcePorts

/-! Every used source-port support cap is actual floor in its real adjacent source tile. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem port_inner_support_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point) (face : Direction) (incoming : Bool)
    (hp : LocalPort (CellPlan.cell (v,pos)) face incoming)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos (boundaryInnerSupport w face incoming)) :
    q ∉ (inventory w hw v).walls := by
  obtain ⟨c,hc,hgood,n,hn,he⟩ := local_port_inner_support_row w hw (CellPlan.cell (v,pos)) face incoming hp
  apply row_floor w hw v pos c (code_mem_of_local w v pos (.line c) hc) hgood n hn q
  simpa only [he] using hq

theorem port_cap_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (pos : GridRouting.Point) (face : Direction) (incoming : Bool)
    (hp : LocalPort (CellPlan.cell (v,pos)) face incoming)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos (boundaryCap w face incoming)) :
    q ∉ (inventory w hw v).walls := by
  obtain ⟨r,hn,_⟩ := CellPlan.used_neighbor v hP hT pos face (local_port_used v pos face incoming hp)
  have hport := local_port_reciprocal v hP hT pos r face hn incoming hp
  apply port_inner_support_floor w hw v r face.opposite (!incoming) hport q
  exact hq.trans (boundary_cap_seam w face pos r incoming hn)

end PushPuzzle.PushS.FiniteSourceInventory
