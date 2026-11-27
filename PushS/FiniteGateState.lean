/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateCore

/-! Exact gate inventories with independent box phases at a propagation frontier. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateState

open PushFS FiniteGeometry

/-- Every physical AND box has an independent current phase. -/
@[ext] structure AndPhases (w : ℕ) where
  west : Fin (w+4) → Bool
  upper : Fin (w+5) → Bool
  middle : Fin 4
  lower : Fin (w+5) → Bool
  guard : Fin (3*w+5) → Bool
  triggerA : Fin 3
  branchB : Fin (4*w+16) → Bool
  branchC : Fin (w+5) → Bool

/-- Ordinary boxes use their two slots; I and A include their temporary positions. -/
def andMixedCell (w : ℕ) (s : AndPhases w) : AndLabel w → Cell (side w) (side w)
  | .west i => andCell w (s.west i) false false (.west i)
  | .upper i => andCell w (s.upper i) false false (.upper i)
  | .middle =>
      (⟨origin w-6*w-9, by unfold origin side; omega⟩,
       ⟨origin w-3*w-9-s.middle.val, by unfold origin side; omega⟩)
  | .lower i => andCell w (s.lower i) false false (.lower i)
  | .guard i => andCell w (s.guard i) false false (.guard i)
  | .triggerA =>
      (⟨origin w+2+s.triggerA.val, by have := s.triggerA.isLt; unfold origin side; omega⟩,
       ⟨origin w, by unfold origin side; omega⟩)
  | .branchB i => andCell w false (s.branchB i) false (.branchB i)
  | .branchC i => andCell w false false (s.branchC i) (.branchC i)

def andMixedBoxes (w : ℕ) (s : AndPhases w) : Finset (Cell (side w) (side w)) :=
  Finset.univ.image (andMixedCell w s)

def andNormalPhases (w : ℕ) (a b c : Bool) : AndPhases w where
  west := fun _ => a
  upper := fun _ => a
  middle := if a then 3 else 0
  lower := fun _ => a
  guard := fun _ => a
  triggerA := if a then 0 else 1
  branchB := fun _ => b
  branchC := fun _ => c

@[simp] theorem andMixedCell_normal (w : ℕ) (a b c : Bool) (l : AndLabel w) :
    andMixedCell w (andNormalPhases w a b c) l = andCell w a b c l := by
  cases l <;> cases a <;> rfl

@[simp] theorem andMixedBoxes_normal (w : ℕ) (a b c : Bool) :
    andMixedBoxes w (andNormalPhases w a b c) = andBoxes w a b c := by
  unfold andMixedBoxes andBoxes
  congr 1
  funext l
  exact andMixedCell_normal w a b c l

/-- Independent OR phases along its three physical branches. -/
@[ext] structure OrPhases (w : ℕ) where
  left : Fin (w+5) → Bool
  triggerA : Bool
  branchB : Fin (w+7) → Bool
  branchC : Fin (w+5) → Bool

def orMixedCell (w : ℕ) (s : OrPhases w) : OrLabel w → Cell (side w) (side w)
  | .left i => orCell w (s.left i) false false (.left i)
  | .triggerA => orCell w s.triggerA false false .triggerA
  | .branchB i => orCell w false (s.branchB i) false (.branchB i)
  | .branchC i => orCell w false false (s.branchC i) (.branchC i)

def orMixedBoxes (w : ℕ) (s : OrPhases w) : Finset (Cell (side w) (side w)) :=
  Finset.univ.image (orMixedCell w s)

def orNormalPhases (w : ℕ) (a b c : Bool) : OrPhases w where
  left := fun _ => a
  triggerA := a
  branchB := fun _ => b
  branchC := fun _ => c

@[simp] theorem orMixedCell_normal (w : ℕ) (a b c : Bool) (l : OrLabel w) :
    orMixedCell w (orNormalPhases w a b c) l = orCell w a b c l := by
  cases l <;> rfl

@[simp] theorem orMixedBoxes_normal (w : ℕ) (a b c : Bool) :
    orMixedBoxes w (orNormalPhases w a b c) = orBoxes w a b c := by
  unfold orMixedBoxes orBoxes
  congr 1
  funext l
  exact orMixedCell_normal w a b c l

end PushPuzzle.PushS.FiniteGateState
