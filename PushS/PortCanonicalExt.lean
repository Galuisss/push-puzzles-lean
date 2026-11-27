/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortCanonicalSignals
import all PushS.PortCanonicalSignals
import all PushS.PortLayoutPolyTime
import all PushS.PortSegments
import CslibFrontier.Foundations.Data.List.FlatMapPositions

/-! Every canonical internal position belongs to its actual emitted group. -/

public section
namespace PushPuzzle.PushS.PortLayout


/-- Each actual internal position reads its native WIRE or three-port canonical bit. -/
theorem canonical_slot_read (l : PortLayout) (axes : List Bool) {g : Placement}
    (hg : g ∈ placements l) {j : ℕ} (hj : j < (if g.gate.isSome then 3 else 1)) :
    (l.canonical axes).internal.getD (g.internal + j) false =
      (if g.gate.isSome then if j = 0 then axes.getD g.left false else !(axes.getD g.right false)
      else if g.side = .upper then !(axes.getD g.left false) else axes.getD g.left false) := by
  cases hk : g.gate with
  | none =>
    have hj0 : j = 0 := by
      simp only [hk, Option.isSome_none, Bool.false_eq_true, ite_false] at hj
      omega
    subst j
    simpa only [Nat.add_zero, hk, Option.isSome_none, Bool.false_eq_true, ite_false] using
      l.canonical_wire_read axes hg hk
  | some kind =>
    have hj3 : j < 3 := by simpa only [hk, Option.isSome_some, ite_true] using hj
    have hs := l.canonical_gate_read axes hg hk
    simp only [Option.isSome_some, ite_true]
    by_cases h0 : j = 0
    · simpa only [h0, Nat.add_zero, ite_true] using hs.1
    · by_cases h1 : j = 1
      · simpa only [h1, Nat.one_ne_zero, ite_false] using hs.2.1
      · have h2 : j = 2 := by omega
        simpa only [h2, OfNat.ofNat_ne_zero, ite_false] using hs.2.2

/-- Canonical slots depend only on the actual left input and, at gates, the actual heavy input. -/
theorem canonical_slot_congr (l : PortLayout) (axes other : List Bool) {g : Placement}
    (hg : g ∈ placements l) {j : ℕ} (hj : j < (if g.gate.isSome then 3 else 1))
    (hleft : axes.getD g.left false = other.getD g.left false)
    (hright : g.gate.isSome = true → axes.getD g.right false = other.getD g.right false) :
    (l.canonical axes).internal.getD (g.internal + j) false =
      (l.canonical other).internal.getD (g.internal + j) false := by
  rw [l.canonical_slot_read axes hg hj, l.canonical_slot_read other hg hj, hleft]
  split
  · rename_i hgate
    rw [hright hgate]
  · rfl

private theorem canonical_slot_owner (l : PortLayout) (axes : List Bool) {k : ℕ}
    (hk : k < (l.canonical axes).internal.length) :
    ∃ g ∈ placements l, ∃ j < (if g.gate.isSome then 3 else 1), k = g.internal + j := by
  by_cases hu : k < l.upperPairs.length
  · let ab := l.upperPairs[k]
    refine ⟨⟨.upper, ab.1, ab.2, l.upperLevel k, k, none⟩, ?_, 0, by change 0 < 1; omega, by exact (Nat.add_zero k).symm⟩
    apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨(ab, k), List.mem_zipIdx_iff_getElem?.mpr (by simp only [List.getElem?_eq_getElem hu]; rfl), rfl⟩
  · have hk' : k - l.upperPairs.length < (l.lowerGroups.flatMap (lowerSignals axes)).length := by
      change k < ((_ ++ l.lowerGroups.flatMap (lowerSignals axes)) : List Bool).length at hk
      simp only [List.length_append, List.length_map] at hk
      omega
    obtain ⟨i, hi, j, hj, hkj⟩ := List.exists_flatMap_prefix_add l.lowerGroups (lowerSignals axes) hk'
    have hm : (l.lowerGroups[i], i) ∈ l.lowerGroups.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr (by simp only [List.getElem?_eq_getElem hi])
    have hcount : j < l.lowerGroups[i].internalCount := by
      simpa only [lowerSignals_length] using hj
    have hoff : k = l.lowerOffset i + j := by
      rw [lowerSignals_flatMap_length] at hkj
      unfold lowerOffset
      omega
    cases he : l.lowerGroups[i] with
    | wire a b =>
      refine ⟨⟨.lower, a, b, l.lowerLevel i, l.lowerOffset i, none⟩, ?_, j, ?_, hoff⟩
      · apply List.mem_append_right
        apply List.mem_map.mpr
        refine ⟨(.wire a b, i), ?_, rfl⟩
        simpa only [he] using hm
      · change j < 1
        simpa only [he, LowerGroup.internalCount] using hcount
    | gate kind first =>
      refine ⟨⟨.lower, first, first + 2, l.lowerLevel i, l.lowerOffset i, some kind⟩, ?_, j, ?_, hoff⟩
      · apply List.mem_append_right
        apply List.mem_map.mpr
        refine ⟨(.gate kind first, i), ?_, rfl⟩
        simpa only [he] using hm
      · change j < 3
        simpa only [he, LowerGroup.internalCount] using hcount

/-- Actual group-slot reads determine the complete canonical internal array. -/
theorem canonical_internal_ext (l : PortLayout) (axes : List Bool) (bits : List Bool)
    (hlen : bits.length = (l.canonical axes).internal.length)
    (hread : ∀ g ∈ placements l, ∀ j < (if g.gate.isSome then 3 else 1),
      bits.getD (g.internal + j) false = (l.canonical axes).internal.getD (g.internal + j) false) :
    bits = (l.canonical axes).internal := by
  apply List.ext_getElem hlen
  intro k hk hk'
  obtain ⟨g, hg, j, hj, rfl⟩ := canonical_slot_owner l axes hk'
  simpa only [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk'] using hread g hg j hj

/-- Actual interface bits and group-slot reads determine the complete canonical physical state. -/
theorem canonical_ext (l : PortLayout) (axes : List Bool) (state : SignalState)
    (haxes : state.axes = axes) (hlen : state.internal.length = (l.canonical axes).internal.length)
    (hread : ∀ g ∈ placements l, ∀ j < (if g.gate.isSome then 3 else 1),
      state.internal.getD (g.internal + j) false = (l.canonical axes).internal.getD (g.internal + j) false) :
    state = l.canonical axes := by
  have hi := l.canonical_internal_ext axes state.internal hlen hread
  cases state with
  | mk ax bits => exact congrArg₂ SignalState.mk haxes hi

end PushPuzzle.PushS.PortLayout
