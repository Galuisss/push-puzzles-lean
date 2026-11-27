/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingTurns
public import PushFS.GuardCorner
public import PushFS.AxisStencil
public import PushFS.AxisIsometry
public import PushFS.IsometryInterior
import Mathlib.Tactic.FinCases

/-! Minimal oriented concave wall stencils for every actual emitted routing turn. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Turn

open PushFS FiniteTools FiniteGeometry

attribute [local irreducible] FiniteTools.side

def stencilEmbedding (w : ℕ) : GridEmbedding 7 7 (FiniteTools.side w) (FiniteTools.side w) :=
  GridEmbedding.translate (radius w-3) (radius w-3)
    (by unfold FiniteTools.side radius; omega) (by unfold FiniteTools.side radius; omega)

private theorem stencil_walls (w : ℕ) (hw : 2 ≤ w) (p : Cell 7 7)
    (hp : p ∈ (GuardStencils.cornerBoard (3 : Fin 7) (3 : Fin 7)).walls) :
    (stencilEmbedding w).cells p ∈ turnWalls w := by
  have hpx := p.1.isLt
  have hpy := p.2.isLt
  have hX : ((stencilEmbedding w).cells p).1.val = radius w-3+p.1.val := rfl
  have hY : ((stencilEmbedding w).cells p).2.val = radius w-3+p.2.val := rfl
  change p ∈ (Finset.univ.filter fun q : Cell 7 7 =>
    (q.2.val+1 = 3 ∧ q.1.val ≤ 3+1) ∨ (q.1.val = 3+1 ∧ 3 ≤ q.2.val+1)) at hp
  rcases (Finset.mem_filter.mp hp).2 with hy | hx
  · apply Finset.mem_biUnion.mpr
    refine ⟨0,Finset.mem_univ _,?_⟩
    apply (Rectangle.mem_cells (turnRectangle w 0) _ _ _).mpr
    rw [hX,hY]
    simp [turnRectangle,radius] at *
    omega
  · apply Finset.mem_biUnion.mpr
    refine ⟨1,Finset.mem_univ _,?_⟩
    apply (Rectangle.mem_cells (turnRectangle w 1) _ _ _).mpr
    rw [hX,hY]
    simp [turnRectangle,radius] at *
    omega

def quarterAxis (n : ℕ) : Direction → AxisIsometry n n n n
  | .east => AxisIsometry.refl _ _
  | .south => AxisIsometry.clockwise _ _
  | .west => (AxisIsometry.reflectX _ _).trans (AxisIsometry.reflectY _ _)
  | .north => (AxisIsometry.reflectX _ _).trans (AxisIsometry.transpose _ _)

def orientationAxis (n : ℕ) (incoming outgoing : Direction) : AxisIsometry n n n n :=
  (if outgoing = rightTurn incoming then AxisIsometry.refl _ _ else AxisIsometry.reflectY _ _).trans
    (quarterAxis n incoming)

/-- Centered odd-square stencils commute with the literal physical rotation or reflection. -/
theorem orientation_stencil (w : ℕ) (d e : Direction) (p : Cell 7 7) :
    (orientation w d e).cells ((stencilEmbedding w).cells p) =
      (stencilEmbedding w).cells ((orientationAxis 7 d e).geometry.cells p) := by
  have hpx := p.1.isLt
  have hpy := p.2.isLt
  cases d <;> cases e <;> apply Prod.ext <;> apply Fin.ext <;>
    simp [orientation,quarter,orientationAxis,quarterAxis,rightTurn,
      AxisIsometry.trans,AxisIsometry.refl,AxisIsometry.clockwise,AxisIsometry.reflectX,
      AxisIsometry.reflectY,AxisIsometry.transpose,GridIsometry.trans,GridIsometry.refl,
      GridIsometry.clockwise,GridIsometry.reflectX,GridIsometry.reflectY,GridIsometry.transpose,
      GridIsometry.symm,stencilEmbedding,GridEmbedding.translate,Fin.revPerm,Fin.rev,
      FiniteTools.side,radius] <;> omega

def stencilClassifier (d e : Direction) :
    AxisClassifier ((orientationAxis 7 d e).geometry.board
      (GuardStencils.cornerBoard (3 : Fin 7) (3 : Fin 7))) :=
  (orientationAxis 7 d e).classifier (GuardStencils.cornerClassifier 3 3) (by
    intro p q hp hd
    exact (AxisTrack.strongAllowed_iff _ p q).mp (GuardStencils.corner_strong hp hd))

/-- Each actual turn has a seven-cell window containing both owned normal slots and its sink. -/
def stencilChart (w : ℕ) (d e : Direction) :
    TranslatedAxisChart (FiniteTools.side w) (FiniteTools.side w) where
  width := 7
  height := 7
  board := (orientationAxis 7 d e).geometry.board (GuardStencils.cornerBoard 3 3)
  dx := radius w-3
  dy := radius w-3
  fits_x := by unfold FiniteTools.side radius; omega
  fits_y := by unfold FiniteTools.side radius; omega
  classifier := stencilClassifier d e

theorem stencilChart_walls (w : ℕ) (hw : 2 ≤ w) (d e : Direction) (p : Cell 7 7)
    (hp : p ∈ (stencilChart w d e).board.walls) :
    (stencilChart w d e).embedding.cells p ∈ ((orientation w d e).board ⟨turnWalls w,∅⟩).walls := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  change (stencilEmbedding w).cells ((orientationAxis 7 d e).geometry.cells q) ∈ _
  rw [← orientation_stencil]
  exact Finset.mem_map.mpr ⟨(stencilEmbedding w).cells q,stencil_walls w hw q hq,rfl⟩

def stencilSlot (phase : Bool) (i : Fin 2) : Cell 7 7 :=
  if i = 0 then (⟨1+phase.toNat,by have := Bool.toNat_le phase; omega⟩,3)
  else (3,⟨4+phase.toNat,by have := Bool.toNat_le phase; omega⟩)

theorem stencilSlot_cell (w : ℕ) (phase : Bool) (i : Fin 2) :
    (stencilEmbedding w).cells (stencilSlot phase i) = cell w phase i := by
  fin_cases i <;> cases phase <;> apply Prod.ext <;> apply Fin.ext <;>
    simp [stencilSlot,stencilEmbedding,GridEmbedding.translate,cell,label,
      turnMixedCell,turnMixedPoint,radius]

theorem stencilSlot_tag (phase : Bool) (i : Fin 2) :
    (GuardStencils.cornerClassifier (3 : Fin 7) (3 : Fin 7)).name (stencilSlot phase i) =
      if i = 0 then .horizontal 3 else .vertical 3 := by
  fin_cases i <;> cases phase <;> decide

/-- Every real owned turn slot, in both phases and every orientation, is represented by the stencil. -/
theorem stencilChart_normal_active (w : ℕ) (d e : Direction) (phase : Bool) (i : Fin 2) :
    ∃ q, (stencilChart w d e).embedding.cells q = (orientation w d e).cells (cell w phase i) ∧
      (stencilChart w d e).classifier.name q ≠ .outside := by
  refine ⟨(orientationAxis 7 d e).geometry.cells (stencilSlot phase i),?_,?_⟩
  · change (stencilEmbedding w).cells ((orientationAxis 7 d e).geometry.cells (stencilSlot phase i)) = _
    rw [← orientation_stencil,stencilSlot_cell]
  · change (orientationAxis 7 d e).name
      ((GuardStencils.cornerClassifier (3 : Fin 7) (3 : Fin 7)).name
        ((orientationAxis 7 d e).geometry.cells.symm
          ((orientationAxis 7 d e).geometry.cells (stencilSlot phase i)))) ≠ .outside
    rw [Equiv.symm_apply_apply]
    intro hh
    have hn := ((orientationAxis 7 d e).outside _).mp hh
    rw [stencilSlot_tag] at hn
    split_ifs at hn

/-- The literal route corner retains its singleton sink name after every orientation. -/
theorem stencilChart_corner (w : ℕ) (d e : Direction) :
    AxisTrack.shift (radius w-3) (radius w-3)
      ((stencilChart w d e).classifier.name ((3,3) : Cell 7 7)) = .sink (radius w) (radius w) := by
  have hn : (stencilChart w d e).classifier.name ((3,3) : Cell 7 7) = .sink 3 3 := by
    change (stencilClassifier d e).name (3,3) = .sink 3 3
    cases d <;> cases e <;> decide
  rw [hn]
  change AxisTrack.sink (radius w-3+3) (radius w-3+3) = _
  congr 1

private theorem stencil_interior_or_ends (p : Cell 7 7)
    (hp : (GuardStencils.cornerClassifier (3 : Fin 7) (3 : Fin 7)).name p ≠ .outside) :
    Interior p ∨ p = ((0,3) : Cell 7 7) ∨ p = ((3,6) : Cell 7 7) := by
  rcases p with ⟨x,y⟩
  fin_cases x <;> fin_cases y <;>
    simp [GuardStencils.cornerClassifier,GuardStencils.cornerName,Fin.ext_iff] at hp <;> decide

/-- Only two actual outward rail cells need owners from the adjacent straight pieces. -/
theorem stencilChart_interior_or_ends (w : ℕ) (d e : Direction) (p : Cell 7 7)
    (hp : (stencilChart w d e).classifier.name p ≠ .outside) :
    Interior p ∨
      (stencilChart w d e).embedding.cells p =
        (orientation w d e).cells ((stencilEmbedding w).cells ((0,3) : Cell 7 7)) ∨
      (stencilChart w d e).embedding.cells p =
        (orientation w d e).cells ((stencilEmbedding w).cells ((3,6) : Cell 7 7)) := by
  obtain ⟨q,rfl⟩ := (orientationAxis 7 d e).geometry.cells.surjective p
  change (orientationAxis 7 d e).name ((GuardStencils.cornerClassifier (3 : Fin 7) (3 : Fin 7)).name
    ((orientationAxis 7 d e).geometry.cells.symm ((orientationAxis 7 d e).geometry.cells q))) ≠ .outside at hp
  rw [Equiv.symm_apply_apply] at hp
  have hq : (GuardStencils.cornerClassifier (3 : Fin 7) (3 : Fin 7)).name q ≠ .outside :=
    fun hh => hp (((orientationAxis 7 d e).outside _).mpr hh)
  rcases stencil_interior_or_ends q hq with hi | rfl | rfl
  · exact Or.inl ((orientationAxis 7 d e).geometry.interior hi)
  · exact Or.inr (Or.inl (orientation_stencil w d e ((0,3) : Cell 7 7)).symm)
  · exact Or.inr (Or.inr (orientation_stencil w d e ((3,6) : Cell 7 7)).symm)

end PushPuzzle.PushS.FiniteRouting.Turn
