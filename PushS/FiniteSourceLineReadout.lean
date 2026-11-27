/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceReadoutLabels
public import PushS.FiniteRoutingNormalOrientation

/-! The actual compiled line's owned labels become exact canonical translated slots after straightening the whole board. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

variable (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)

attribute [local irreducible] width height codes Line.width Line.height

structure LineSite (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) where
  index : Fin (codes w v).length
  code : LineCode
  code_eq : ((codes w v).get index).2 = .line code

namespace LineSite

variable {w hw v} (s : LineSite w hw v)

def atoms : List Line.Atom := Line.program w (segmentLength s.code.segment) (s.code.above != s.code.desiredSide)
def orientation : RectOrientation := Line.rectangleOrientation (segmentDirection s.code.segment)
def dx : ℕ := (inventory w hw v).dx s.index
def dy : ℕ := (inventory w hw v).dy s.index

def label (l : (PrimitiveCode.line s.code).Labels w) : (inventory w hw v).PhysicalLabel :=
  primitiveLabel w hw v s.index (.line s.code) s.code_eq l


private theorem sizes :
    ((PrimitiveCode.line s.code).instanceOf w hw).width = s.orientation.width (Line.width w s.atoms) (Line.height w) ∧
    ((PrimitiveCode.line s.code).instanceOf w hw).height = s.orientation.height (Line.width w s.atoms) (Line.height w) := by
  cases hd : segmentDirection s.code.segment <;>
    simp only [PrimitiveCode.instanceOf,lineInstance,GridIsometry.reorientInstance,orientation,hd,Line.rectangleOrientation,
      RectOrientation.width,RectOrientation.height,Bool.false_eq_true,ite_true,ite_false,atoms] <;> exact ⟨rfl,rfl⟩

theorem fits :
    s.dx+s.orientation.width (Line.width w s.atoms) (Line.height w) ≤ width w v ∧
      s.dy+s.orientation.height (Line.width w s.atoms) (Line.height w) ≤ height w v := by
  have hx := (inventory w hw v).fitsX s.index
  have hy := (inventory w hw v).fitsY s.index
  change s.dx+(((codes w v).get s.index).2.instanceOf w hw).width ≤ width w v at hx
  change s.dy+(((codes w v).get s.index).2.instanceOf w hw).height ≤ height w v at hy
  rw [s.code_eq,s.sizes.1] at hx
  rw [s.code_eq,s.sizes.2] at hy
  exact ⟨hx,hy⟩

def canonicalEmbedding : GridEmbedding (Line.width w s.atoms) (Line.height w)
    (s.orientation.inverse.width (width w v) (height w v)) (s.orientation.inverse.height (width w v) (height w v)) :=
  s.orientation.normalizedEmbedding s.fits.1 s.fits.2

theorem dx_eq : s.dx = tileStride w*((codes w v).get s.index).1.1+PrimitiveCode.offsetX w (.line s.code) := by
  change tileStride w*((codes w v).get s.index).1.1+PrimitiveCode.offsetX w ((codes w v).get s.index).2 = _
  rw [s.code_eq]

theorem dy_eq : s.dy = tileStride w*((codes w v).get s.index).1.2+PrimitiveCode.offsetY w (.line s.code) := by
  change tileStride w*((codes w v).get s.index).1.2+PrimitiveCode.offsetY w ((codes w v).get s.index).2 = _
  rw [s.code_eq]

theorem source_normal (l : (PrimitiveCode.line s.code).Labels w) :
    (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells ((inventory w hw v).source (s.label l)) =
      s.canonicalEmbedding.cells (Line.cell w hw s.atoms s.code.initial l.val) := by
  change Line.OwnedLabel w s.atoms s.code.first s.code.last at l
  apply s.orientation.normalized_cell s.fits.1 s.fits.2
  have hs := source_primitiveLabel_coordinates w hw v s.index (.line s.code) s.code_eq l
  change coordinates ((inventory w hw v).source (s.label l)) = _ at hs
  dsimp only [coordinates] at hs
  rw [hs,s.dx_eq,s.dy_eq]
  have hr := Line.rectangleOrientation_point w s.atoms (segmentDirection s.code.segment)
    (Line.cell w hw s.atoms s.code.initial l.val)
  change _ =
    ((tileStride w*((codes w v).get s.index).1.1+PrimitiveCode.offsetX w (.line s.code))+
      (s.orientation.point (Line.width w s.atoms) (Line.height w) (coordinates (Line.cell w hw s.atoms s.code.initial l.val))).1,
     (tileStride w*((codes w v).get s.index).1.2+PrimitiveCode.offsetY w (.line s.code))+
      (s.orientation.point (Line.width w s.atoms) (Line.height w) (coordinates (Line.cell w hw s.atoms s.code.initial l.val))).2)
  change shiftPoint (tileStride w*((codes w v).get s.index).1.1) (tileStride w*((codes w v).get s.index).1.2)
    (shiftPoint (PrimitiveCode.offsetX w (.line s.code)) (PrimitiveCode.offsetY w (.line s.code))
      (coordinates ((Line.rotation w s.atoms (segmentDirection s.code.segment)).cells
        (Line.cell w hw s.atoms s.code.initial l.val)))) = _
  unfold orientation
  rw [←hr]
  simp only [shiftPoint,coordinates,Nat.add_assoc]

theorem target_normal (l : (PrimitiveCode.line s.code).Labels w) :
    (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells ((inventory w hw v).target (s.label l)) =
      s.canonicalEmbedding.cells (Line.cell w hw s.atoms s.code.target l.val) := by
  change Line.OwnedLabel w s.atoms s.code.first s.code.last at l
  apply s.orientation.normalized_cell s.fits.1 s.fits.2
  have hs := target_primitiveLabel_coordinates w hw v s.index (.line s.code) s.code_eq l
  change coordinates ((inventory w hw v).target (s.label l)) = _ at hs
  dsimp only [coordinates] at hs
  rw [hs,s.dx_eq,s.dy_eq]
  have hr := Line.rectangleOrientation_point w s.atoms (segmentDirection s.code.segment)
    (Line.cell w hw s.atoms s.code.target l.val)
  change _ =
    ((tileStride w*((codes w v).get s.index).1.1+PrimitiveCode.offsetX w (.line s.code))+
      (s.orientation.point (Line.width w s.atoms) (Line.height w) (coordinates (Line.cell w hw s.atoms s.code.target l.val))).1,
     (tileStride w*((codes w v).get s.index).1.2+PrimitiveCode.offsetY w (.line s.code))+
      (s.orientation.point (Line.width w s.atoms) (Line.height w) (coordinates (Line.cell w hw s.atoms s.code.target l.val))).2)
  change shiftPoint (tileStride w*((codes w v).get s.index).1.1) (tileStride w*((codes w v).get s.index).1.2)
    (shiftPoint (PrimitiveCode.offsetX w (.line s.code)) (PrimitiveCode.offsetY w (.line s.code))
      (coordinates ((Line.rotation w s.atoms (segmentDirection s.code.segment)).cells
        (Line.cell w hw s.atoms s.code.target l.val)))) = _
  unfold orientation
  rw [←hr]
  simp only [shiftPoint,coordinates,Nat.add_assoc]

end LineSite
end PushPuzzle.PushS.FiniteSourceInventory
