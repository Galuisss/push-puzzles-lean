/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceLineReadout

/-! Literal compiled walls and the common macro/readout floor in the normalized full-board line rectangle. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

variable (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)

attribute [local irreducible] width height codes Line.width Line.height Line.walls InventoryAssembly.walls InventoryAssembly.board

theorem primitiveEmbedding_coordinates (i : Fin (codes w v).length) (c : PrimitiveCode)
    (he : ((codes w v).get i).2 = c) (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height) :
    coordinates ((primitiveEmbedding w hw v i c he).cells p) =
      shiftPoint ((inventory w hw v).dx i) ((inventory w hw v).dy i) (coordinates p) := by
  subst c
  rfl

namespace LineSite

variable {w hw v} (s : LineSite w hw v)

def actualEmbedding : GridEmbedding (Line.width w s.atoms) (Line.height w) (width w v) (height w v) :=
  (Line.rotation w s.atoms (segmentDirection s.code.segment)).embedding.trans
    (primitiveEmbedding w hw v s.index (.line s.code) s.code_eq)

/-- All literal normal and nonnormal local cells use the same actual canonical placement. -/
theorem placed_normal (p : Cell (Line.width w s.atoms) (Line.height w)) :
    (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells (s.actualEmbedding.cells p) =
      s.canonicalEmbedding.cells p := by
  apply s.orientation.normalized_cell s.fits.1 s.fits.2
  have hp := primitiveEmbedding_coordinates w hw v s.index (.line s.code) s.code_eq
    ((Line.rotation w s.atoms (segmentDirection s.code.segment)).cells p)
  have hr := Line.rectangleOrientation_point w s.atoms (segmentDirection s.code.segment) p
  change coordinates (s.actualEmbedding.cells p) = _ at hp
  dsimp only [coordinates] at hp
  rw [hp]
  change shiftPoint s.dx s.dy (coordinates ((Line.rotation w s.atoms (segmentDirection s.code.segment)).cells p)) = _
  rw [hr]
  rfl

set_option maxHeartbeats 1000000 in
/-- The normalized glyph's walls are actual members of the compiled global union. -/
theorem wall_normal (p : Cell (Line.width w s.atoms) (Line.height w)) (hp : p ∈ Line.walls w s.atoms s.code.above) :
    s.canonicalEmbedding.cells p ∈
      ((s.orientation.inverse.axis (width w v) (height w v)).geometry.board (inventory w hw v).board).walls := by
  have hp' : (Line.rotation w s.atoms (segmentDirection s.code.segment)).cells p ∈
      ((PrimitiveCode.line s.code).instanceOf w hw).board.walls := by
    change (Line.rotation w s.atoms (segmentDirection s.code.segment)).cells p ∈
      (Line.walls w s.atoms s.code.above).map (Line.rotation w s.atoms (segmentDirection s.code.segment)).cells.toEmbedding
    exact Finset.mem_map.mpr ⟨p,hp,rfl⟩
  have hh := wall_primitiveEmbedding w hw v s.index (.line s.code) s.code_eq _ hp'
  change s.actualEmbedding.cells p ∈ (inventory w hw v).walls at hh
  have hhb : s.actualEmbedding.cells p ∈ (inventory w hw v).board.walls := by
    simpa only [InventoryAssembly.board] using hh
  rw [←s.placed_normal]
  exact Finset.mem_map.mpr ⟨s.actualEmbedding.cells p,hhb,rfl⟩

def ownedLabel (hfirst : s.code.first = false) (l : Line.OwnedLabel w s.atoms false s.code.last) :
    (inventory w hw v).PhysicalLabel :=
  s.label ⟨l.val,by simpa only [hfirst,atoms] using l.property⟩

theorem source_owned (hfirst : s.code.first = false) (l : Line.OwnedLabel w s.atoms false s.code.last) :
    (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells
      ((inventory w hw v).source (s.ownedLabel hfirst l)) =
        s.canonicalEmbedding.cells (Line.ownedCell w hw s.atoms false s.code.last s.code.initial l) :=
  s.source_normal _

theorem target_owned (hfirst : s.code.first = false) (l : Line.OwnedLabel w s.atoms false s.code.last) :
    (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells
      ((inventory w hw v).target (s.ownedLabel hfirst l)) =
        s.canonicalEmbedding.cells (Line.ownedCell w hw s.atoms false s.code.last s.code.target l) :=
  s.target_normal _

end LineSite
end PushPuzzle.PushS.FiniteSourceInventory
