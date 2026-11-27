/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateSelected

/-! Every prepared gate stock is a concrete independent phase inventory. -/

public section
namespace PushPuzzle.PushS.FiniteGateState

open PushFS FiniteGeometry FiniteGateCore FiniteGateMacros FiniteGateVertical
open FiniteGateOutputs FiniteGateInputs FiniteGateBTemporary
open scoped Classical

attribute [local irreducible] side

/-- B's ordinary tail is prepared while its trigger is still low. -/
def andBPhases (w : ℕ) (a c q : Bool) : AndPhases w :=
  { andNormalPhases w a false c with branchB := fun i => if i = 0 then false else q }

/-- The OR B-tail phase with its first trigger held low. -/
def orBPhases (w : ℕ) (a c q : Bool) : OrPhases w :=
  { orNormalPhases w a false c with branchB := fun i => if i = 0 then false else q }

@[simp] private theorem andMixedCell_B (w : ℕ) (a c q : Bool) (l : AndLabel w) :
    andMixedCell w (andBPhases w a c q) l = andBCell w a c q l := by
  cases l <;> cases a <;> rfl

@[simp] theorem andMixedBoxes_B (w : ℕ) (a c q : Bool) :
    andMixedBoxes w (andBPhases w a c q) = andBBoxes w a c q := by
  unfold andMixedBoxes andBBoxes
  congr 1
  funext l
  exact andMixedCell_B w _ _ _ l

@[simp] private theorem orMixedCell_B (w : ℕ) (a c q : Bool) (l : OrLabel w) :
    orMixedCell w (orBPhases w a c q) l = orBCell w a c q l := by
  cases l <;> rfl

@[simp] theorem orMixedBoxes_B (w : ℕ) (a c q : Bool) :
    orMixedBoxes w (orBPhases w a c q) = orBBoxes w a c q := by
  unfold orMixedBoxes orBBoxes
  congr 1
  funext l
  exact orMixedCell_B w _ _ _ l

/-- C's trigger has moved while its ordinary tail remains in the specified phase. -/
def andOutputPhases (w : ℕ) (a b q : Bool) : AndPhases w :=
  { andNormalPhases w a b true with branchC := fun i => if i = 0 then true else q }

/-- The OR output phase with its first C trigger held high. -/
def orOutputPhases (w : ℕ) (a b q : Bool) : OrPhases w :=
  { orNormalPhases w a b true with branchC := fun i => if i = 0 then true else q }

@[simp] theorem andMixedCell_output (w : ℕ) (a b q : Bool) (l : AndLabel w) :
    andMixedCell w (andOutputPhases w a b q) l = andOutputCell w a b q l := by
  cases l <;> cases a <;> rfl

@[simp] theorem andMixedBoxes_output (w : ℕ) (a b q : Bool) :
    andMixedBoxes w (andOutputPhases w a b q) = andOutputBoxes w a b q := by
  unfold andMixedBoxes andOutputBoxes
  congr 1
  funext l
  exact andMixedCell_output w _ _ _ l

@[simp] theorem orMixedCell_output (w : ℕ) (a b q : Bool) (l : OrLabel w) :
    orMixedCell w (orOutputPhases w a b q) l = orOutputCell w a b q l := by
  cases l <;> rfl

@[simp] theorem orMixedBoxes_output (w : ℕ) (a b q : Bool) :
    orMixedBoxes w (orOutputPhases w a b q) = orOutputBoxes w a b q := by
  unfold orMixedBoxes orOutputBoxes
  congr 1
  funext l
  exact orMixedCell_output w _ _ _ l

/-- The OR left tail is prepared while its trigger keeps the closed slot. -/
def orInputPhases (w : ℕ) (b c q : Bool) : OrPhases w :=
  { orNormalPhases w false b c with left := fun _ => q }

@[simp] private theorem orMixedCell_input (w : ℕ) (b c q : Bool) (l : OrLabel w) :
    orMixedCell w (orInputPhases w b c q) l = orInputCell w b c q l := by
  cases l <;> rfl

@[simp] theorem orMixedBoxes_input (w : ℕ) (b c q : Bool) :
    orMixedBoxes w (orInputPhases w b c q) = orInputBoxes w b c q := by
  unfold orMixedBoxes orInputBoxes
  congr 1
  funext l
  exact orMixedCell_input w _ _ _ l

/-- The closed-A B program's temporary rightmost A slot. -/
@[expose] def andTemporaryPhases (w : ℕ) : AndPhases w :=
  { andNormalPhases w false true false with triggerA := 2 }

@[simp] theorem andMixedBoxes_temporary (w : ℕ) (hw : 2 ≤ w) :
    andMixedBoxes w (andTemporaryPhases w) = temporaryBoxes w := by
  have hr := FiniteWireFrame.image_relocate (andCell w false true false)
    (andMixedCell w (andTemporaryPhases w)) (andCell_injective w hw false true false) .triggerA
    (by intro l hl; cases l <;> simp_all [andMixedCell,andTemporaryPhases,andNormalPhases,andCell,andPoint])
  exact hr.symm

end PushPuzzle.PushS.FiniteGateState
