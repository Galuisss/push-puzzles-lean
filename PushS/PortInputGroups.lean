/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortCanonicalSignals
import all PushS.PortLayoutPolyTime
import all PushS.PortSegments
import Mathlib.Data.List.Enum

/-! The actual emitted WIRE and AND/OR thresholds characterize the existing original input arrays. -/

public section
namespace PushPuzzle.PushS.PortLayout


private theorem indexed_mem {α : Type} {xs : List α} {x : α} (hx : x ∈ xs) : ∃ i, (x, i) ∈ xs.zipIdx := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
  have h : ∃ p ∈ xs.zipIdx, p = (x, i) := List.exists_mem_zipIdx'.mpr ⟨i, hi, by simp only [he]⟩
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨i, hp⟩

/-- Checking every actual emitted group gives exactly the existing native input legality. -/
theorem InputLegal.of_placements (l : PortLayout) (axes : List Bool) (hlen : axes.length = l.portCount)
    (hwire : ∀ g ∈ l.placements, g.gate = none →
      if g.side = .upper then axes.getD g.left false = true ∨ axes.getD g.right false = true
      else axes.getD g.left false = false ∨ axes.getD g.right false = false)
    (hgate : ∀ g ∈ l.placements, ∀ kind, g.gate = some kind →
      if kind = .andGate then axes.getD g.right false = false ∨
        (axes.getD g.left false = false ∧ axes.getD (g.left + 1) false = false)
      else axes.getD g.left false = false ∨ axes.getD (g.left + 1) false = false ∨ axes.getD g.right false = false) :
    l.InputLegal axes := by
  refine ⟨hlen, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    obtain ⟨i, hi⟩ := indexed_mem hab
    have hg : (⟨.upper, a, b, l.upperLevel i, i, none⟩ : Placement) ∈ l.placements :=
      List.mem_append_left _ (List.mem_map.mpr ⟨((a, b), i), hi, rfl⟩)
    simpa only [ite_true] using hwire _ hg rfl
  · intro a b hab
    obtain ⟨i, hi⟩ := indexed_mem hab
    have hg : (⟨.lower, a, b, l.lowerLevel i, l.lowerOffset i, none⟩ : Placement) ∈ l.placements :=
      List.mem_append_right _ (List.mem_map.mpr ⟨(.wire a b, i), hi, rfl⟩)
    simpa only [reduceCtorEq, ite_false] using hwire _ hg rfl
  · intro first hfirst
    obtain ⟨i, hi⟩ := indexed_mem hfirst
    have hg : (⟨.lower, first, first + 2, l.lowerLevel i, l.lowerOffset i, some .orGate⟩ : Placement) ∈ l.placements :=
      List.mem_append_right _ (List.mem_map.mpr ⟨(.gate .orGate first, i), hi, rfl⟩)
    simpa only [reduceCtorEq, ite_false] using hgate _ hg .orGate rfl
  · intro first hfirst
    obtain ⟨i, hi⟩ := indexed_mem hfirst
    have hg : (⟨.lower, first, first + 2, l.lowerLevel i, l.lowerOffset i, some .andGate⟩ : Placement) ∈ l.placements :=
      List.mem_append_right _ (List.mem_map.mpr ⟨(.gate .andGate first, i), hi, rfl⟩)
    simpa only [ite_true] using hgate _ hg .andGate rfl

end PushPuzzle.PushS.PortLayout
