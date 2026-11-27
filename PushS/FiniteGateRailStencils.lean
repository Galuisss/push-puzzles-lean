/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateStencils
public import PushFS.GuardCorner
public import PushFS.GuardRails
public import PushFS.AxisIsometry
import Mathlib.Tactic.FinCases

/-! The remaining actual AND rails and the two protected corner sinks. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateStencils

open PushFS FiniteGeometry FiniteGateCore

attribute [local irreducible] side

def andVerticalEmbedding (w : ℕ) : GridEmbedding 3 (6*w+22) (side w) (side w) :=
  GridEmbedding.translate (origin w-6*w-10) (origin w-6*w-21)
    (by unfold origin side; omega) (by unfold origin side; omega)

def andVerticalBoard (w : ℕ) : Board 3 (6*w+22) :=
  (andVerticalEmbedding w).pullback (andBoard w ∅)

/-- The guarding side changes twice through the literal vertical flip. -/
theorem andVertical_guard (w : ℕ) (hw : 2 ≤ w) :
    GuardStencils.VerticalGuard (andVerticalBoard w) (1 : Fin 3) := by
  intro y u v hu hv
  have hy := y.isLt
  have hul : u.val = 0 := by omega
  have hvl : v.val = 2 := by omega
  have hleft : ((andVerticalEmbedding w).cells (u,y)).1.val = origin w-6*w-10 := by
    change origin w-6*w-10+u.val = _; omega
  have hright : ((andVerticalEmbedding w).cells (v,y)).1.val = origin w-6*w-8 := by
    change origin w-6*w-10+v.val = _; unfold origin; omega
  have hY (x : Fin 3) : ((andVerticalEmbedding w).cells (x,y)).2.val =
      origin w-6*w-21+y.val := rfl
  by_cases hy0 : y.val+3 ≤ 3*w+12
  · right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨4,Finset.mem_univ _,?_⟩⟩
    apply (Rectangle.mem_cells (andRectangle w 4) _ _ _).mpr
    rw [hright,hY]
    simp [andRectangle,origin] at *
    omega
  · by_cases hy1 : y.val+2 = 3*w+12
    · left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨2,Finset.mem_univ _,?_⟩⟩
      apply (Rectangle.mem_cells (andRectangle w 2) _ _ _).mpr
      rw [hleft,hY]
      simp [andRectangle,origin] at *
      omega
    · by_cases hy2 : y.val+1 = 3*w+12
      · right
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨3,Finset.mem_univ _,?_⟩⟩
        apply (Rectangle.mem_cells (andRectangle w 3) _ _ _).mpr
        rw [hright,hY]
        simp [andRectangle,origin] at *
        omega
      · left
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨1,Finset.mem_univ _,?_⟩⟩
        apply (Rectangle.mem_cells (andRectangle w 1) _ _ _).mpr
        rw [hleft,hY]
        simp [andRectangle,origin] at *
        omega

def andVertical (w : ℕ) (hw : 2 ≤ w) : TranslatedAxisChart (side w) (side w) where
  width := 3
  height := 6*w+22
  board := andVerticalBoard w
  dx := origin w-6*w-10
  dy := origin w-6*w-21
  fits_x := by unfold origin side; omega
  fits_y := by unfold origin side; omega
  classifier := GuardStencils.verticalOfGuard 1 (andVertical_guard w hw)

theorem andVertical_walls (w : ℕ) (hw : 2 ≤ w) :
    (andVertical w hw).embedding.WallsAgree (andVertical w hw).board (andBoard w ∅) :=
  (andVerticalEmbedding w).pullback_walls _

/-- A small exact upper concave stencil, retaining the corner's singleton name. -/
def andUpperCorner (w : ℕ) : TranslatedAxisChart (side w) (side w) where
  width := 3
  height := 3
  board := GuardStencils.cornerBoard (1 : Fin 3) (1 : Fin 3)
  dx := origin w-6*w-10
  dy := origin w-6*w-22
  fits_x := by unfold origin side; omega
  fits_y := by unfold origin side; omega
  classifier := GuardStencils.cornerClassifier 1 1

theorem andUpperCorner_walls (w : ℕ) (hw : 2 ≤ w) (p : Cell 3 3)
    (hp : p ∈ (andUpperCorner w).board.walls) :
    (andUpperCorner w).embedding.cells p ∈ andWalls w := by
  have hpx := p.1.isLt
  have hpy := p.2.isLt
  have hX : ((andUpperCorner w).embedding.cells p).1.val = origin w-6*w-10+p.1.val := rfl
  have hY : ((andUpperCorner w).embedding.cells p).2.val = origin w-6*w-22+p.2.val := rfl
  change p ∈ (Finset.univ.filter fun q : Cell 3 3 =>
    (q.2.val+1 = 1 ∧ q.1.val ≤ 1+1) ∨ (q.1.val = 1+1 ∧ 1 ≤ q.2.val+1)) at hp
  rcases (Finset.mem_filter.mp hp).2 with hy | hx
  · apply Finset.mem_biUnion.mpr
    refine ⟨5,Finset.mem_univ _,?_⟩
    apply (Rectangle.mem_cells (andRectangle w 5) _ _ _).mpr
    rw [hX,hY]
    simp [andRectangle,origin] at *
    omega
  · apply Finset.mem_biUnion.mpr
    refine ⟨4,Finset.mem_univ _,?_⟩
    apply (Rectangle.mem_cells (andRectangle w 4) _ _ _).mpr
    rw [hX,hY]
    simp [andRectangle,origin] at *
    omega

/-- The standard concave stencil turned through two right angles. -/
def protectionAxis : AxisIsometry 3 3 3 3 :=
  (AxisIsometry.reflectX 3 3).trans (AxisIsometry.reflectY 3 3)

def protectionBoard : Board 3 3 :=
  protectionAxis.geometry.board (GuardStencils.cornerBoard (1 : Fin 3) (1 : Fin 3))

def protectionClassifier : AxisClassifier protectionBoard :=
  protectionAxis.classifier (GuardStencils.cornerClassifier 1 1) (by
    intro p q hp hd
    exact (AxisTrack.strongAllowed_iff _ p q).mp (GuardStencils.corner_strong hp hd))

private theorem protectionBoard_wall_iff (p : Cell 3 3) :
    p ∈ protectionBoard.walls ↔ p.2.val = 2 ∨ p.1.val = 0 := by
  rcases p with ⟨x,y⟩
  fin_cases x <;> fin_cases y <;> decide

def andProtectionCorner (w : ℕ) : TranslatedAxisChart (side w) (side w) where
  width := 3
  height := 3
  board := protectionBoard
  dx := origin w-6*w-10
  dy := origin w-1
  fits_x := by unfold origin side; omega
  fits_y := by unfold origin side; omega
  classifier := protectionClassifier

theorem andProtectionCorner_walls (w : ℕ) (hw : 2 ≤ w) (p : Cell 3 3)
    (hp : p ∈ (andProtectionCorner w).board.walls) :
    (andProtectionCorner w).embedding.cells p ∈ andWalls w := by
  have hpx := p.1.isLt
  have hpy := p.2.isLt
  have hX : ((andProtectionCorner w).embedding.cells p).1.val = origin w-6*w-10+p.1.val := rfl
  have hY : ((andProtectionCorner w).embedding.cells p).2.val = origin w-1+p.2.val := rfl
  rcases (protectionBoard_wall_iff p).mp hp with hy | hx
  · apply Finset.mem_biUnion.mpr
    refine ⟨0,Finset.mem_univ _,?_⟩
    apply (Rectangle.mem_cells (andRectangle w 0) _ _ _).mpr
    rw [hX,hY]
    simp [andRectangle,origin] at *
    omega
  · apply Finset.mem_biUnion.mpr
    refine ⟨1,Finset.mem_univ _,?_⟩
    apply (Rectangle.mem_cells (andRectangle w 1) _ _ _).mpr
    rw [hX,hY]
    simp [andRectangle,origin] at *
    omega

def andWestEmbedding (w : ℕ) : GridEmbedding (2*w+11) 3 (side w) (side w) :=
  GridEmbedding.translate (origin w-8*w-18) (origin w-6*w-22)
    (by unfold origin side; omega) (by unfold origin side; omega)

def andWestBoard (w : ℕ) : Board (2*w+11) 3 :=
  (andWestEmbedding w).pullback (andBoard w ∅)

theorem andWest_guard (w : ℕ) (hw : 2 ≤ w) :
    GuardStencils.HorizontalGuard (andWestBoard w) (1 : Fin 3) := by
  intro x u v hu _
  have hx := x.isLt
  have hu0 : u.val = 0 := by omega
  have hX : ((andWestEmbedding w).cells (x,u)).1.val = origin w-8*w-18+x.val := rfl
  have hY : ((andWestEmbedding w).cells (x,u)).2.val = origin w-6*w-22+u.val := rfl
  left
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨5,Finset.mem_univ _,?_⟩⟩
  apply (Rectangle.mem_cells (andRectangle w 5) _ _ _).mpr
  rw [hX,hY]
  simp [andRectangle,origin] at *
  omega

def andWest (w : ℕ) (hw : 2 ≤ w) : TranslatedAxisChart (side w) (side w) where
  width := 2*w+11
  height := 3
  board := andWestBoard w
  dx := origin w-8*w-18
  dy := origin w-6*w-22
  fits_x := by unfold origin side; omega
  fits_y := by unfold origin side; omega
  classifier := GuardStencils.horizontalOfGuard 1 (andWest_guard w hw)

theorem andWest_walls (w : ℕ) (hw : 2 ≤ w) :
    (andWest w hw).embedding.WallsAgree (andWest w hw).board (andBoard w ∅) :=
  (andWestEmbedding w).pullback_walls _

end PushPuzzle.PushS.FiniteGateStencils
