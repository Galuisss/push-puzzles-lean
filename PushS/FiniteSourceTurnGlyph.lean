/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceLineGlyph

/-! Actual compiled F/G ownership, literal walls and exact canonical turn slots after whole-board normalization. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] width height codes Line.width Line.height Line.walls InventoryAssembly.walls InventoryAssembly.board

structure TurnSite (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) where
  index : Fin (codes w v).length
  code : TurnCode
  code_eq : ((codes w v).get index).2 = .turn code
  perpendicular : Perpendicular code.incoming code.outgoing

namespace TurnSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : TurnSite w hw v)

def orientation : RectOrientation := Turn.rectangleOrientation s.code.incoming s.code.outgoing
def dx : ℕ := (inventory w hw v).dx s.index
def dy : ℕ := (inventory w hw v).dy s.index

def label (l : Fin 2) : (inventory w hw v).PhysicalLabel := primitiveLabel w hw v s.index (.turn s.code) s.code_eq l

private theorem sizes :
    ((PrimitiveCode.turn s.code).instanceOf w hw).width = s.orientation.width (FiniteTools.side w) (FiniteTools.side w) ∧
    ((PrimitiveCode.turn s.code).instanceOf w hw).height = s.orientation.height (FiniteTools.side w) (FiniteTools.side w) := by
  cases hs : s.orientation.swapAxes <;> simp [PrimitiveCode.instanceOf,Turn.orientedPuzzle,GridIsometry.reorientInstance,
    RectOrientation.width,RectOrientation.height,hs]

theorem fits :
    s.dx+s.orientation.width (FiniteTools.side w) (FiniteTools.side w) ≤ width w v ∧
      s.dy+s.orientation.height (FiniteTools.side w) (FiniteTools.side w) ≤ height w v := by
  have hx := (inventory w hw v).fitsX s.index
  have hy := (inventory w hw v).fitsY s.index
  change s.dx+(((codes w v).get s.index).2.instanceOf w hw).width ≤ width w v at hx
  change s.dy+(((codes w v).get s.index).2.instanceOf w hw).height ≤ height w v at hy
  rw [s.code_eq,s.sizes.1] at hx
  rw [s.code_eq,s.sizes.2] at hy
  exact ⟨hx,hy⟩

def actualEmbedding : GridEmbedding (FiniteTools.side w) (FiniteTools.side w) (width w v) (height w v) :=
  (Turn.orientation w s.code.incoming s.code.outgoing).embedding.trans
    (primitiveEmbedding w hw v s.index (.turn s.code) s.code_eq)

def canonicalEmbedding : GridEmbedding (FiniteTools.side w) (FiniteTools.side w)
    (s.orientation.inverse.width (width w v) (height w v)) (s.orientation.inverse.height (width w v) (height w v)) :=
  s.orientation.normalizedEmbedding s.fits.1 s.fits.2

theorem placed_normal (p : Cell (FiniteTools.side w) (FiniteTools.side w)) :
    (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells (s.actualEmbedding.cells p) = s.canonicalEmbedding.cells p := by
  apply s.orientation.normalized_cell s.fits.1 s.fits.2
  have hp := primitiveEmbedding_coordinates w hw v s.index (.turn s.code) s.code_eq
    ((Turn.orientation w s.code.incoming s.code.outgoing).cells p)
  have hr := Turn.rectangleOrientation_point w s.code.incoming s.code.outgoing s.perpendicular p
  change coordinates (s.actualEmbedding.cells p) = _ at hp
  dsimp only [coordinates] at hp
  rw [hp]
  change shiftPoint s.dx s.dy (coordinates ((Turn.orientation w s.code.incoming s.code.outgoing).cells p)) = _
  rw [hr]
  rfl

theorem source_actual (l : Fin 2) : (inventory w hw v).source (s.label l) = s.actualEmbedding.cells (Turn.cell w s.code.initial l) :=
  source_primitiveLabel w hw v s.index (.turn s.code) s.code_eq l

theorem target_actual (l : Fin 2) : (inventory w hw v).target (s.label l) = s.actualEmbedding.cells (Turn.cell w s.code.target l) :=
  target_primitiveLabel w hw v s.index (.turn s.code) s.code_eq l

theorem source_normal (l : Fin 2) :
    (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells ((inventory w hw v).source (s.label l)) =
      s.canonicalEmbedding.cells (Turn.cell w s.code.initial l) := by rw [s.source_actual,s.placed_normal]

theorem target_normal (l : Fin 2) :
    (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells ((inventory w hw v).target (s.label l)) =
      s.canonicalEmbedding.cells (Turn.cell w s.code.target l) := by rw [s.target_actual,s.placed_normal]

set_option maxHeartbeats 1000000 in
theorem wall_normal (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.turnWalls w) :
    s.canonicalEmbedding.cells p ∈
      ((s.orientation.inverse.axis (width w v) (height w v)).geometry.board (inventory w hw v).board).walls := by
  have hp' : (Turn.orientation w s.code.incoming s.code.outgoing).cells p ∈
      ((PrimitiveCode.turn s.code).instanceOf w hw).board.walls := by
    change _ ∈ (FiniteTools.turnWalls w).map (Turn.orientation w s.code.incoming s.code.outgoing).cells.toEmbedding
    exact Finset.mem_map.mpr ⟨p,hp,rfl⟩
  have hh := wall_primitiveEmbedding w hw v s.index (.turn s.code) s.code_eq _ hp'
  change s.actualEmbedding.cells p ∈ (inventory w hw v).walls at hh
  have hhb : s.actualEmbedding.cells p ∈ (inventory w hw v).board.walls := by
    simpa only [InventoryAssembly.board] using hh
  rw [←s.placed_normal]
  exact Finset.mem_map.mpr ⟨s.actualEmbedding.cells p,hhb,rfl⟩

set_option maxHeartbeats 1000000 in
/-- This actual compiled turn has all source, target and wall fields derived from its code table entry. -/
def glyph (ha : (inventory w hw v).Admissible)
    (hc : ∀ l, SameComponent (inventory w hw v).board ((inventory w hw v).source l) ((inventory w hw v).target l))
    (A : ComponentTracks ((s.orientation.inverse.axis (width w v) (height w v)).geometry.reorientInstance ((inventory w hw v).puzzle ha)))
    (horizontalTag : A.name (s.canonicalEmbedding.cells (Turn.cell w s.code.initial 0)) =
      .horizontal (s.orientation.normalizedY (width w v) (height w v) (FiniteTools.side w) (FiniteTools.side w) s.dx s.dy+FiniteTools.radius w))
    (verticalTag : A.name (s.canonicalEmbedding.cells (Turn.cell w s.code.initial 1)) =
      .vertical (s.orientation.normalizedX (width w v) (height w v) (FiniteTools.side w) (FiniteTools.side w) s.dx s.dy+FiniteTools.radius w))
    (cornerTag : A.name (s.canonicalEmbedding.cells (Turn.center w)) =
      .sink (s.orientation.normalizedX (width w v) (height w v) (FiniteTools.side w) (FiniteTools.side w) s.dx s.dy+FiniteTools.radius w)
        (s.orientation.normalizedY (width w v) (height w v) (FiniteTools.side w) (FiniteTools.side w) s.dx s.dy+FiniteTools.radius w)) :
    Turn.Readout.TurnGlyph (((inventory w hw v).slotMatching ha hc).reorient
      (s.orientation.inverse.axis (width w v) (height w v)).geometry) A w := by
  have hfit := s.orientation.normalized_fits s.fits.1 s.fits.2
  exact Turn.Readout.TurnGlyph.of_slots w hw
    (s.orientation.normalizedX (width w v) (height w v) (FiniteTools.side w) (FiniteTools.side w) s.dx s.dy)
    (s.orientation.normalizedY (width w v) (height w v) (FiniteTools.side w) (FiniteTools.side w) s.dx s.dy)
    hfit.1 hfit.2 s.code.initial s.code.target s.label s.source_normal s.target_normal
    (by change A.name ((s.orientation.inverse.axis (width w v) (height w v)).geometry.cells ((inventory w hw v).source (s.label 0))) = _
        rw [s.source_normal]; exact horizontalTag)
    (by change A.name ((s.orientation.inverse.axis (width w v) (height w v)).geometry.cells ((inventory w hw v).source (s.label 1))) = _
        rw [s.source_normal]; exact verticalTag)
    cornerTag s.wall_normal

end TurnSite
end PushPuzzle.PushS.FiniteSourceInventory
