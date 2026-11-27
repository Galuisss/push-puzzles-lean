/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalPlacements
public import PushFS.Reduction.FullGatePrimitivePlacement

/-! Actual source gate records and all of their real primitives embedded in the complete physical board. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory


open Cslib.Complexity.NCL Plan PhysicalBitmap
set_option maxRecDepth 65536

def gateIndex (v : CellPlan.Source) (g : VertexData) (hg : g∈vertexRecords v.1) : Index v :=
  let p : Raster.Cell v.1 :=
    (⟨(refinePoint g.point).1,by have := Raster.vertex_bounds v.1 hg; omega⟩,
      ⟨(refinePoint g.point).2,by have := Raster.vertex_bounds v.1 hg; omega⟩)
  ⟨(p,.inl (gateTileState (g,v.2))),by
    have hv := (Raster.vertexAt_eq_some_iff v.1 (refinePoint g.point) g).mpr ⟨hg,rfl⟩
    change PhysicalTiles.key (CellPlan.cell (v,refinePoint g.point))=some (.inl (gateTileState (g,v.2)))
    rw [CellPlan.cell_gate v _ hv]
    rfl⟩

theorem gateIndex_position (v : CellPlan.Source) (g : VertexData) (hg : g∈vertexRecords v.1) :
    position (gateIndex v g hg)=refinePoint g.point := rfl

theorem gateIndex_injective (v : CellPlan.Source) {g h : VertexData}
    (hg : g∈vertexRecords v.1) (hh : h∈vertexRecords v.1) (he : gateIndex v g hg=gateIndex v h hh) : g=h := by
  have hp := congrArg position he
  change refinePoint g.point=refinePoint h.point at hp
  have hv := (Raster.vertexAt_eq_some_iff v.1 (refinePoint g.point) g).mpr ⟨hg,rfl⟩
  have hw := (Raster.vertexAt_eq_some_iff v.1 (refinePoint h.point) h).mpr ⟨hh,rfl⟩
  rw [hp,hw] at hv
  exact (Option.some.inj hv).symm

noncomputable def gateEmbedding (v : CellPlan.Source) (g : VertexData) (hg : g∈vertexRecords v.1) :
    GridEmbedding 200007 198068 (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7) :=
  embedding v (gateIndex v g hg)

theorem gate_walls_agree (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) :
    (gateEmbedding v g hg).WallsAgree (GateTileRouting.fullAtlas (gateTileState (g,v.2))).board (atlas v hP hT).board :=
  walls_agree v hP hT (gateIndex v g hg)

noncomputable def gatePrimitiveEmbedding (v : CellPlan.Source) (g : VertexData) (hg : g∈vertexRecords v.1)
    (i : GateTileRouting.Inventory.Index (gateTileState (g,v.2))) :
    GridEmbedding (GateTileRouting.Inventory.piece (gateTileState (g,v.2)) i).width
      (GateTileRouting.Inventory.piece (gateTileState (g,v.2)) i).height
      (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7) :=
  (GateTileRouting.primitiveEmbedding (gateTileState (g,v.2)) i).trans (gateEmbedding v g hg)

/-- Every actual core, lead, complete annular line and protected short corner keeps its exact walls on the whole board. -/
theorem gate_primitive_walls (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) (i : GateTileRouting.Inventory.Index (gateTileState (g,v.2))) :
    (gatePrimitiveEmbedding v g hg i).WallsAgree
      (GateTileRouting.Inventory.piece (gateTileState (g,v.2)) i).board (atlas v hP hT).board := by
  intro p
  exact (gate_walls_agree v hP hT g hg ((GateTileRouting.primitiveEmbedding (gateTileState (g,v.2)) i).cells p)).trans
    (GateTileRouting.primitive_walls_agree (gateTileState (g,v.2)) i p)

end PushPuzzle.PushFS.Reduction.PhysicalInventory
