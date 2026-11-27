/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.StaticSlots
public import PushFS.StaticPlacement
import Mathlib.Tactic.FinCases

/-!
# Actual axis classification of both complete long-wall gates

The AND has two vertical rails, two horizontal rails and two protected sink
corners. The OR has one vertical and one horizontal rail. Kernel stencil checks
cover every finite-board displacement from a represented rail or sink.
Ambient reflection is available at interior sources through `StaticPlacement`.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Gates


/-- Actual row/column/sink names of the uniformly oriented long-wall gate. -/
def axisName (kind : Bool) (p : C) : AxisTrack :=
  if trackTest kind p then
    if kind then
      if p = (39,90) then .sink 39 90
      else if p = (39,29) then .sink 39 29
      else if p.2.val = 90 then .horizontal 90
      else if p.1.val = 39 then .vertical 39
      else if p.2.val = 29 ∧ p.1.val < 39 then .horizontal 29
      else .vertical 43
    else if p.2.val = 90 then .horizontal 90 else .vertical 44
  else .outside

-- These finite certificates inspect all 81×107 cells and each active cell's four stencils.
set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem supported_checked : ∀ (kind : Bool) (p : C),
    AxisTrack.supportTest (axisName kind) p = true := by decide +kernel

theorem displacements_checked : ∀ kind : Bool,
    checkDisplacements (wallTest kind) (AxisTrack.activeSources (axisName kind))
      (AxisTrack.allowed (axisName kind)) = true := by
  have checked : ∀ (kind : Bool) (x : Fin 81) (y : Fin 107) (d : Direction),
      axisName kind (x, y) ≠ .outside →
      (staticStep (wallTest kind) d (x, y)).elim true
        (AxisTrack.allowed (axisName kind) (x, y)) = true := by
    intro kind x
    cases kind <;> fin_cases x <;> decide +kernel
  intro kind
  simp only [checkDisplacements, decide_eq_true_eq]
  intro p hp d
  exact checked kind p.1 p.2 d (Finset.mem_filter.mp hp).2

/-- Complete finite-board classification from the real wall predicate. -/
def classifier (kind : Bool) (goals : Finset C) : AxisClassifier (board kind goals) :=
  AxisClassifier.of_check (wallTest_correct kind goals) (axisName kind)
    (supported_checked kind) (displacements_checked kind)

private theorem slots_active_checked : ∀ kind : Bool,
    ((slots kind).all fun s => decide (axisName kind s.zero ≠ .outside) &&
      decide (axisName kind s.one ≠ .outside)) = true := by decide +kernel

/-- Both canonical positions of every actual physical slot lie on an active axis track. -/
theorem slot_position_active (kind : Bool) (s : Slot) (hs : s ∈ slots kind) (b : Signals) :
    axisName kind (s.position b) ≠ .outside := by
  have hh := List.all_eq_true.mp (slots_active_checked kind) s hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
  unfold Slot.position
  split
  · exact hh.2
  · exact hh.1

private def separatedTest (kind : Bool) (b : Signals) : Bool :=
  (positions kind b).all fun p => (positions kind b).all fun q =>
    if axisName kind p = axisName kind q then decide (∀ d : Direction, ¬Adjacent d p q) else true

private theorem separated_checked : ∀ (kind a b c : Bool), separatedTest kind ⟨a,b,c⟩ = true := by
  intro kind a b c
  cases kind <;> cases a <;> cases b <;> cases c <;> decide +kernel

/-- Canonical goals on any one named rail are never adjacent. -/
theorem normal_separated (kind : Bool) (b : Signals) :
    ∀ p ∈ canonicalBoxes kind b, ∀ q ∈ canonicalBoxes kind b,
      axisName kind p = axisName kind q → ∀ d, ¬Adjacent d p q := by
  intro p hp q hq he
  have hh := List.all_eq_true.mp (List.all_eq_true.mp
    (separated_checked kind b.left b.upper b.right) p (List.mem_toFinset.mp hp))
      q (List.mem_toFinset.mp hq)
  simpa only [he, ↓reduceIte, decide_eq_true_eq] using hh

end PushPuzzle.PushFS.Gadgets.Gates
