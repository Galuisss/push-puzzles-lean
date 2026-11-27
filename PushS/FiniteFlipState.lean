/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteTools
public import PushS.FiniteWireFrame
import Mathlib.Tactic.FinCases

/-! Exact thick-flip inventories and the active floor used for ambient replay. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteTools

open PushFS

/-- Only this bounded strip of actual floor is used by the flip macros. -/
def flipActive (w : ℕ) : Finset (Cell (side w) (side w)) :=
  Finset.univ.filter fun p =>
    radius w-w-2 ≤ p.1.val ∧ p.1.val ≤ radius w+w+5 ∧
      radius w-w-1 ≤ p.2.val ∧ p.2.val ≤ radius w+w+1 ∧ p ∉ flipWalls w

/-- Extra proof walls reserve every cell outside the actual active footprint. -/
def flipMacroBoard (w : ℕ) : Board (side w) (side w) :=
  FiniteWireFrame.board (flipActive w) ∅

/-- Both endpoint phases and all three intermediate positions of the middle box. -/
def flipMixedCell (w : ℕ) (a : Bool) (m : Fin 4) (b : Bool) :
    FlipLabel → Cell (side w) (side w)
  | .predecessor => flipCell w false .predecessor
  | .left => flipCell w a .left
  | .middle =>
    (⟨radius w+m.val, by have := m.isLt; unfold side radius; omega⟩,
     ⟨radius w, by unfold side radius; omega⟩)
  | .right => flipCell w b .right
  | .successor => flipCell w false .successor

def flipMixedBoxes (w : ℕ) (a : Bool) (m : Fin 4) (b : Bool) :
    Finset (Cell (side w) (side w)) := Finset.univ.image (flipMixedCell w a m b)

theorem flipMixedCell_injective (w : ℕ) (hw : 2 ≤ w) (a : Bool) (m : Fin 4) (b : Bool) :
    Function.Injective (flipMixedCell w a m b) := by
  intro i j he
  have heX := congrArg (fun p : Cell (side w) (side w) => p.1.val) he
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hm := m.isLt
  cases i <;> cases j <;>
    dsimp [flipMixedCell, flipCell, flipPoint, radius] at heX <;> first | rfl | omega

theorem flipMixedCell_active (w : ℕ) (a : Bool) (m : Fin 4) (b : Bool) (l : FlipLabel) :
    flipMixedCell w a m b l ∈ flipActive w := by
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hm := m.isLt
  simp only [flipActive, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases l <;> dsimp [flipMixedCell, flipCell, flipPoint, radius] <;> omega
  · cases l <;> dsimp [flipMixedCell, flipCell, flipPoint, radius] <;> omega
  · cases l <;> dsimp [flipMixedCell, flipCell, flipPoint, radius] <;> omega
  · cases l <;> dsimp [flipMixedCell, flipCell, flipPoint, radius] <;> omega
  · intro hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    have hi' := ((flipRectangle w i).mem_cells _ _ _).mp hi
    fin_cases i <;> cases l <;>
      simp [flipRectangle, flipMixedCell, flipCell, flipPoint, radius] at hi' <;> omega

theorem flipMixedBoxes_floor (w : ℕ) (a : Bool) (m : Fin 4) (b : Bool) :
    Disjoint (flipMixedBoxes w a m b) (flipMacroBoard w).walls := by
  apply Finset.disjoint_left.mpr
  intro p hp
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
  exact (FiniteWireFrame.floor_iff _ _ _).mpr (flipMixedCell_active w a m b l)

/-- All turning points and supports of both complete flip executions. -/
inductive FlipNode
  | rightSupport | right0 | lowerRight | lowerMouthOuter | lowerMouth
  | upperMouth | upperMouthOuter | left1UpperOuter | left1 | middleSupport
  | middle0 | middle3 | leftSupportUpperOuter | leftSupport | left0
  | leftReverseSupport | middleReverseSupport | rightSupportLowerOuter | rightReverseSupport | right1
  deriving DecidableEq

def flipNodePoint (w : ℕ) : FlipNode → ℕ × ℕ
  | .rightSupport => (radius w+w+1, radius w)
  | .right0 => (radius w+w+2, radius w)
  | .lowerRight => (radius w+w+2, radius w+w+1)
  | .lowerMouthOuter => (radius w+1, radius w+w+1)
  | .lowerMouth => (radius w+1, radius w)
  | .upperMouth => (radius w+2, radius w)
  | .upperMouthOuter => (radius w+2, radius w-w-1)
  | .left1UpperOuter => (radius w+1-w, radius w-w-1)
  | .left1 => (radius w+1-w, radius w)
  | .middleSupport => (radius w-1, radius w)
  | .middle0 => (radius w, radius w)
  | .middle3 => (radius w+3, radius w)
  | .leftSupportUpperOuter => (radius w-w-1, radius w-w-1)
  | .leftSupport => (radius w-w-1, radius w)
  | .left0 => (radius w-w, radius w)
  | .leftReverseSupport => (radius w+2-w, radius w)
  | .middleReverseSupport => (radius w+4, radius w)
  | .rightSupportLowerOuter => (radius w+w+4, radius w+w+1)
  | .rightReverseSupport => (radius w+w+4, radius w)
  | .right1 => (radius w+w+3, radius w)

theorem flipNodePoint_interior (w : ℕ) (i : FlipNode) :
    (flipNodePoint w i).1 < side w ∧ (flipNodePoint w i).2 < side w := by
  cases i <;> dsimp [flipNodePoint, radius, side] <;> omega

def flipNode (w : ℕ) (i : FlipNode) : Cell (side w) (side w) :=
  (⟨(flipNodePoint w i).1, (flipNodePoint_interior w i).1⟩,
   ⟨(flipNodePoint w i).2, (flipNodePoint_interior w i).2⟩)

theorem flipNode_active (w : ℕ) (i : FlipNode) : flipNode w i ∈ flipActive w := by
  simp only [flipActive, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases i <;> dsimp [flipNode, flipNodePoint, radius] <;> omega
  · cases i <;> dsimp [flipNode, flipNodePoint, radius] <;> omega
  · cases i <;> dsimp [flipNode, flipNodePoint, radius] <;> omega
  · cases i <;> dsimp [flipNode, flipNodePoint, radius] <;> omega
  · intro hp
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
    have hj' := ((flipRectangle w j).mem_cells _ _ _).mp hj
    fin_cases j <;> cases i <;>
      simp [flipRectangle, flipNode, flipNodePoint, radius] at hj' <;> omega

end PushPuzzle.PushS.FiniteTools
