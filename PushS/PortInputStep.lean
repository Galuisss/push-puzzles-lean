/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortInputLegal
import Mathlib.Data.List.GetD

/-!
# Single-axis moves on the actual native port inputs

A move flips exactly one existing contour axis between legal inputs. Ordered moves retain the
same original interface constraints and the AND light-input order at both ends. Reachability
uses the standard reflexive-transitive closure of these move relations.

## Main definitions

* `PortLayout.AxisStep`: one original axis flip between legal actual inputs.
* `PortLayout.OrderedAxisStep`: the same flip between ordered actual inputs.

## Main results

* `PortLayout.OrderedAxisStep.toAxisStep`: forget the additional input order.
* `PortLayout.AxisStep.symm`, `OrderedAxisStep.symm`: every actual axis flip is reversible.
-/

public section

namespace PushPuzzle.PushS.PortLayout


/-- Flip exactly one existing actual axis between two legal native interface vectors. -/
@[expose] def AxisStep (l : PortLayout) (axes next : List Bool) : Prop :=
  l.InputLegal axes ∧ ∃ i, i < l.portCount ∧
    next = axes.set i (!(axes.getD i false)) ∧ l.InputLegal next

/-- Flip the same single existing axis between two ordered native interface vectors. -/
@[expose] def OrderedAxisStep (l : PortLayout) (axes next : List Bool) : Prop :=
  l.OrderedInputs axes ∧ ∃ i, i < l.portCount ∧
    next = axes.set i (!(axes.getD i false)) ∧ l.OrderedInputs next

/-- An ordered actual axis flip is a legal native axis flip. -/
theorem OrderedAxisStep.toAxisStep {l : PortLayout} {axes next : List Bool}
    (h : l.OrderedAxisStep axes next) : l.AxisStep axes next := by
  obtain ⟨hs, i, hi, he, ht⟩ := h
  exact ⟨hs.toInputLegal, i, hi, he, ht.toInputLegal⟩

private theorem getD_flip (axes : List Bool) (i : ℕ) (hi : i < axes.length) :
    (axes.set i (!(axes.getD i false))).getD i false = !(axes.getD i false) := by
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_set] using hi)]
  exact List.getElem_set_self (by simpa only [List.length_set] using hi)

private theorem flip_twice (axes : List Bool) (i : ℕ) (hi : i < axes.length) :
    (axes.set i (!(axes.getD i false))).set i
      (!((axes.set i (!(axes.getD i false))).getD i false)) = axes := by
  rw [getD_flip axes i hi, Bool.not_not, List.set_set,
    List.getD_eq_getElem _ _ hi, List.set_getElem_self hi]

private theorem flip_step_symm (count : ℕ) (P : List Bool → Prop)
    (hlen : ∀ a, P a → a.length = count) {axes next : List Bool}
    (h : P axes ∧ ∃ i, i < count ∧ next = axes.set i (!(axes.getD i false)) ∧ P next) :
    P next ∧ ∃ i, i < count ∧ axes = next.set i (!(next.getD i false)) ∧ P axes := by
  obtain ⟨hs, i, hi, rfl, ht⟩ := h
  have ha : i < axes.length := by rw [hlen axes hs]; exact hi
  exact ⟨ht, i, hi, (flip_twice axes i ha).symm, hs⟩

/-- Reversing a legal actual axis flip returns to the same original interface vector. -/
theorem AxisStep.symm {l : PortLayout} {axes next : List Bool}
    (h : l.AxisStep axes next) : l.AxisStep next axes :=
  flip_step_symm l.portCount l.InputLegal (fun _ h => h.axes_length) h

/-- Reversing an ordered actual axis flip retains both original ordered inputs. -/
theorem OrderedAxisStep.symm {l : PortLayout} {axes next : List Bool}
    (h : l.OrderedAxisStep axes next) : l.OrderedAxisStep next axes :=
  flip_step_symm l.portCount l.OrderedInputs (fun _ h => h.axes_length) h

end PushPuzzle.PushS.PortLayout
