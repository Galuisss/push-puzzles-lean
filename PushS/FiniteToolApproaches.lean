/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteFlipMacros
public import PushS.FiniteTurnMacros
import Mathlib.Tactic.FinCases

/-! Actual entry and exit walks between exposed tool lanes and their internal support cells. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteTools

open PushFS

attribute [local irreducible] side

def turnHorizontalEntry (w : ℕ) : Cell (side w) (side w) :=
  (⟨radius w-2, by unfold side radius; omega⟩, ⟨radius w+1, by unfold side radius; omega⟩)

def turnVerticalEntry (w : ℕ) : Cell (side w) (side w) :=
  (⟨radius w-1, by unfold side radius; omega⟩, ⟨radius w+2, by unfold side radius; omega⟩)

inductive TurnAccess
  | horizontalAcross | horizontalInto | verticalUp | verticalInto | exitHorizontal | exitVertical

namespace TurnAccess

def phase : TurnAccess → Bool
  | .horizontalAcross | .horizontalInto | .exitHorizontal => true
  | _ => false

def start (w : ℕ) : TurnAccess → Cell (side w) (side w)
  | .horizontalAcross => turnHorizontalEntry w
  | .horizontalInto => turnNode w .vertical0
  | .verticalUp => turnVerticalEntry w
  | .verticalInto => turnNode w .horizontal1
  | .exitHorizontal => turnNode w .horizontal0
  | .exitVertical => turnNode w .vertical1

def finish (w : ℕ) : TurnAccess → Cell (side w) (side w)
  | .horizontalAcross => turnNode w .vertical0
  | .horizontalInto | .verticalInto => turnNode w .corner
  | .verticalUp => turnNode w .horizontal1
  | .exitHorizontal => turnHorizontalEntry w
  | .exitVertical => turnVerticalEntry w

private theorem free (w : ℕ) (a : TurnAccess) (p : Cell (side w) (side w))
    (hx : min (a.start w).1.val (a.finish w).1.val ≤ p.1.val)
    (hx' : p.1.val ≤ max (a.start w).1.val (a.finish w).1.val)
    (hy : min (a.start w).2.val (a.finish w).2.val ≤ p.2.val)
    (hy' : p.2.val ≤ max (a.start w).2.val (a.finish w).2.val) :
    Free (turnMacroBoard w) (turnBoxes w a.phase) p := by
  constructor
  · apply (FiniteWireFrame.floor_iff _ _ _).mpr
    rw [turnActive, FiniteGeometry.Rectangle.mem_cells]
    cases a <;> dsimp [start, finish, turnHorizontalEntry, turnVerticalEntry, turnNode, turnNodePoint, radius]
      at hx hx' hy hy' ⊢ <;> omega
  · intro hp
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hp
    have hpx := congrArg (fun p => p.1.val) he
    have hpy := congrArg (fun p => p.2.val) he
    cases a <;> cases l <;>
      simp only [phase, start, finish, turnHorizontalEntry, turnVerticalEntry, turnNode, turnNodePoint,
        turnMixedCell, turnMixedPoint, radius, Bool.toNat_true, Bool.toNat_false] at hpx hpy hx hx' hy hy' <;> omega

private theorem walk (w : ℕ) (a : TurnAccess) :
    Reachable (turnMacroBoard w) (some 1)
      ⟨a.start w, turnBoxes w a.phase⟩ ⟨a.finish w, turnBoxes w a.phase⟩ :=
  FiniteWireFrame.walk_rectangle (turnMixedBoxes_floor w a.phase a.phase) _ _ (a.free w)

end TurnAccess

theorem turn_enter_horizontal (w : ℕ) :
    Reachable (turnMacroBoard w) (some 1)
      ⟨turnHorizontalEntry w, turnBoxes w true⟩ ⟨turnNode w .corner, turnBoxes w true⟩ :=
  (TurnAccess.horizontalAcross.walk w).trans (TurnAccess.horizontalInto.walk w)

theorem turn_enter_vertical (w : ℕ) :
    Reachable (turnMacroBoard w) (some 1)
      ⟨turnVerticalEntry w, turnBoxes w false⟩ ⟨turnNode w .corner, turnBoxes w false⟩ :=
  (TurnAccess.verticalUp.walk w).trans (TurnAccess.verticalInto.walk w)

theorem turn_exit_horizontal (w : ℕ) :
    Reachable (turnMacroBoard w) (some 1)
      ⟨turnNode w .horizontal0, turnBoxes w true⟩ ⟨turnHorizontalEntry w, turnBoxes w true⟩ :=
  TurnAccess.exitHorizontal.walk w

theorem turn_exit_vertical (w : ℕ) :
    Reachable (turnMacroBoard w) (some 1)
      ⟨turnNode w .vertical1, turnBoxes w false⟩ ⟨turnVerticalEntry w, turnBoxes w false⟩ :=
  TurnAccess.exitVertical.walk w

def flipUpperExit (w : ℕ) : Cell (side w) (side w) :=
  (⟨radius w-w, by unfold side radius; omega⟩, ⟨radius w-1, by unfold side radius; omega⟩)

def flipLowerExit (w : ℕ) : Cell (side w) (side w) :=
  (⟨radius w+w+3, by unfold side radius; omega⟩, ⟨radius w+1, by unfold side radius; omega⟩)

inductive FlipAccess
  | forwardVertical | forwardHorizontal | backwardVertical | backwardHorizontal | exitUpper | exitLower

namespace FlipAccess

def phase : FlipAccess → Bool
  | .backwardVertical | .backwardHorizontal | .exitUpper => true
  | _ => false

def start (w : ℕ) : FlipAccess → Cell (side w) (side w)
  | .forwardVertical => flipNode w .lowerMouthOuter
  | .forwardHorizontal => flipNode w .lowerMouth
  | .backwardVertical => flipNode w .upperMouthOuter
  | .backwardHorizontal => flipNode w .upperMouth
  | .exitUpper => flipNode w .left0
  | .exitLower => flipNode w .right1

def finish (w : ℕ) : FlipAccess → Cell (side w) (side w)
  | .forwardVertical => flipNode w .lowerMouth
  | .forwardHorizontal => flipNode w .rightSupport
  | .backwardVertical => flipNode w .upperMouth
  | .backwardHorizontal => flipNode w .leftReverseSupport
  | .exitUpper => flipUpperExit w
  | .exitLower => flipLowerExit w

set_option maxHeartbeats 1000000 in
private theorem free (w : ℕ) (hw : 2 ≤ w) (a : FlipAccess) (p : Cell (side w) (side w))
    (hx : min (a.start w).1.val (a.finish w).1.val ≤ p.1.val)
    (hx' : p.1.val ≤ max (a.start w).1.val (a.finish w).1.val)
    (hy : min (a.start w).2.val (a.finish w).2.val ≤ p.2.val)
    (hy' : p.2.val ≤ max (a.start w).2.val (a.finish w).2.val) :
    Free (flipMacroBoard w) (flipBoxes w a.phase) p := by
  constructor
  · apply (FiniteWireFrame.floor_iff _ _ _).mpr
    simp only [flipActive, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try (cases a <;>
      dsimp [start, finish, flipUpperExit, flipLowerExit, flipNode, flipNodePoint, radius] at hx hx' hy hy' ⊢ <;> omega)
    intro hp
    obtain ⟨i, hi, hm⟩ := Finset.mem_biUnion.mp hp
    have hm' := ((flipRectangle w i).mem_cells _ _ _).mp hm
    fin_cases i <;> cases a <;>
      simp [flipRectangle, start, finish, flipUpperExit, flipLowerExit, flipNode, flipNodePoint, radius]
        at hm' hx hx' hy hy' <;> omega
  · intro hp
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hp
    have hpx := congrArg (fun p => p.1.val) he
    have hpy := congrArg (fun p => p.2.val) he
    cases a <;> cases l <;>
      simp only [phase, start, finish, flipUpperExit, flipLowerExit, flipNode, flipNodePoint,
        flipCell, flipPoint, radius, Bool.toNat_true, Bool.toNat_false] at hpx hpy hx hx' hy hy' <;> omega

private theorem walk (w : ℕ) (hw : 2 ≤ w) (a : FlipAccess) :
    Reachable (flipMacroBoard w) (some 1)
      ⟨a.start w, flipBoxes w a.phase⟩ ⟨a.finish w, flipBoxes w a.phase⟩ :=
  FiniteWireFrame.walk_rectangle (flipMixedBoxes_floor w a.phase ⟨3*a.phase.toNat, by have := Bool.toNat_le a.phase; omega⟩ a.phase)
    _ _ (a.free w hw)

end FlipAccess

theorem flip_enter_forward (w : ℕ) (hw : 2 ≤ w) :
    Reachable (flipMacroBoard w) (some 1)
      ⟨flipNode w .lowerMouthOuter, flipBoxes w false⟩ ⟨flipNode w .rightSupport, flipBoxes w false⟩ :=
  (FlipAccess.forwardVertical.walk w hw).trans (FlipAccess.forwardHorizontal.walk w hw)

theorem flip_enter_backward (w : ℕ) (hw : 2 ≤ w) :
    Reachable (flipMacroBoard w) (some 1)
      ⟨flipNode w .upperMouthOuter, flipBoxes w true⟩ ⟨flipNode w .leftReverseSupport, flipBoxes w true⟩ :=
  (FlipAccess.backwardVertical.walk w hw).trans (FlipAccess.backwardHorizontal.walk w hw)

theorem flip_exit_upper (w : ℕ) (hw : 2 ≤ w) :
    Reachable (flipMacroBoard w) (some 1)
      ⟨flipNode w .left0, flipBoxes w true⟩ ⟨flipUpperExit w, flipBoxes w true⟩ :=
  FlipAccess.exitUpper.walk w hw

theorem flip_exit_lower (w : ℕ) (hw : 2 ≤ w) :
    Reachable (flipMacroBoard w) (some 1)
      ⟨flipNode w .right1, flipBoxes w false⟩ ⟨flipLowerExit w, flipBoxes w false⟩ :=
  FlipAccess.exitLower.walk w hw

end PushPuzzle.PushS.FiniteTools
