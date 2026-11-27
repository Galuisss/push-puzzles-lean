/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortCanonicalExt
public import PushS.PortAxisGroups
import all PushS.PortGateIndexing
import all PushS.PortWireIndexing
import all PushS.PortCoreCrossing
import all PushS.PortSegments
import CslibFrontier.Foundations.Data.List.Lookup

/-! Exact finite internal updates for one canonical interface-axis change. -/

public section
namespace PushPuzzle.PushS.PortLayout


/-- Set the canonical internal slots of this group affected by one interface-axis value. -/
@[expose] def Placement.canonicalUpdate (g : Placement) (bits : List Bool) (port : ℕ) (gain : Bool) : List Bool :=
  if g.left = port then bits.set g.internal (if g.side = .upper then !gain else gain)
  else if g.gate.isSome = true ∧ g.right = port then
    (bits.set (g.internal + 1) (!gain)).set (g.internal + 2) (!gain)
  else bits

/-- Updating the actual affected internal slots preserves their allocated array length. -/
theorem Placement.canonicalUpdate_length (g : Placement) (bits : List Bool) (port : ℕ) (gain : Bool) :
    (g.canonicalUpdate bits port gain).length = bits.length := by
  unfold canonicalUpdate
  split
  · exact List.length_set
  · split
    · simp only [List.length_set]
    · rfl

private theorem canonicalUpdate_other (l : PortLayout) {g h : Placement}
    (hg : g ∈ placements l) (hh : h ∈ placements l) (hne : g ≠ h)
    (bits : List Bool) (port : ℕ) (gain : Bool) {j : ℕ}
    (hj : j < (if h.gate.isSome then 3 else 1)) :
    (g.canonicalUpdate bits port gain).getD (h.internal + j) false = bits.getD (h.internal + j) false := by
  have hindex {i : ℕ} (hi : i < (if g.gate.isSome then 3 else 1)) :
      g.internal + i ≠ h.internal + j := by
    intro heq
    apply hne
    apply placement_slot_overlap l hg hh (k := g.internal + i)
    · change g.internal ≤ g.internal + i ∧ g.internal + i < g.internal + (if g.gate.isSome then 3 else 1)
      omega
    · change h.internal ≤ g.internal + i ∧ g.internal + i < h.internal + (if h.gate.isSome then 3 else 1)
      omega
  unfold Placement.canonicalUpdate
  split
  · exact List.getD_set_ne (by simpa only [Nat.add_zero] using hindex (i := 0) (by split <;> omega))
  · split
    · rename_i hgate
      have hi1 := hindex (i := 1) (by simp only [hgate.1, ite_true]; omega)
      have hi2 := hindex (i := 2) (by simp only [hgate.1, ite_true]; omega)
      rw [List.getD_set_ne hi2, List.getD_set_ne hi1]
    · rfl

private theorem read_set (bits : List Bool) {i : ℕ} (hi : i < bits.length) (value : Bool) (j : ℕ) :
    (bits.set i value).getD j false = if i = j then value else bits.getD j false := by
  by_cases he : i = j
  · subst j
    simp only [ite_true, List.getD_set_self hi]
  · rw [List.getD_set_ne he, ite_eq_right he]

private theorem canonicalUpdate_own (l : PortLayout) (hl : l.pages.Valid) {g : Placement}
    (hg : g ∈ placements l) (axes bits : List Bool)
    (hlen : bits.length = (l.canonical axes).internal.length)
    (hread : ∀ j < (if g.gate.isSome then 3 else 1),
      bits.getD (g.internal + j) false = (l.canonical axes).internal.getD (g.internal + j) false)
    {port : ℕ} (hp : port < axes.length) (gain : Bool) {j : ℕ}
    (hj : j < (if g.gate.isSome then 3 else 1)) :
    (g.canonicalUpdate bits port gain).getD (g.internal + j) false =
      (l.canonical (axes.set port gain)).internal.getD (g.internal + j) false := by
  have hb := l.canonical_placement_bounds axes hg
  have hb0 : g.internal < bits.length := by
    rw [hlen]
    split at hb <;> omega
  have hold := (hread j hj).trans (l.canonical_slot_read axes hg hj)
  rw [l.canonical_slot_read (axes.set port gain) hg hj, read_set axes hp gain g.left,
    read_set axes hp gain g.right]
  cases hk : g.gate with
  | none =>
    have hj0 : j = 0 := by simp only [hk, Option.isSome_none, Bool.false_eq_true, ite_false] at hj; omega
    subst j
    simp only [hk, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] at hold ⊢
    unfold Placement.canonicalUpdate
    simp only [hk, Option.isSome_none, Bool.false_eq_true, false_and, ite_false]
    by_cases he : g.left = port
    · simp only [he, ite_true, read_set bits hb0]
    · simp only [he, Ne.symm he, ite_false]
      exact hold
  | some kind =>
    have hs := (placement_gate_shape l hg hk).1
    have hlt := (gate_port_bounds l hl hg hk).1
    have hj3 : j < 3 := by simpa only [hk, Option.isSome_some, ite_true] using hj
    have hb3 : g.internal + 3 ≤ bits.length := by
      simpa only [hk, Option.isSome_some, ite_true, ← hlen] using hb
    have hb1 : g.internal + 1 < bits.length := by omega
    have hb2 : g.internal + 2 < bits.length := by omega
    simp only [hk, Option.isSome_some, ite_true, hs, reduceCtorEq, ite_false] at hold ⊢
    unfold Placement.canonicalUpdate
    simp only [hs, reduceCtorEq, ite_false, hk, Option.isSome_some, true_and]
    by_cases hleft : g.left = port
    · have hright : port ≠ g.right := by omega
      simp only [hleft, ite_true, read_set bits hb0, hright, ite_false]
      by_cases hj0 : j = 0
      · simp only [hj0, Nat.add_zero, ite_true]
      · have hidx : g.internal ≠ g.internal + j := by omega
        simp only [hidx, hj0, ite_false]
        simpa only [hj0, ite_false] using hold
    · simp only [hleft, Ne.symm hleft, ite_false]
      by_cases hright : g.right = port
      · simp only [hright, ite_true]
        rw [read_set (bits.set (g.internal + 1) (!gain)) (by simpa only [List.length_set] using hb2) (!gain) (g.internal + j),
          read_set bits hb1 (!gain) (g.internal + j)]
        by_cases hj0 : j = 0
        · simp only [hj0, Nat.add_zero, show g.internal + 2 ≠ g.internal by omega,
            show g.internal + 1 ≠ g.internal by omega, ite_false, ite_true]
          simpa only [hj0, ite_true, Nat.add_zero] using hold
        · by_cases hj1 : j = 1
          · simp only [hj1, show g.internal + 2 ≠ g.internal + 1 by omega, ite_false, ite_true, Nat.one_ne_zero]
          · have hj2 : j = 2 := by omega
            simp only [hj2, ite_true, OfNat.ofNat_ne_zero, ite_false]
      · simp only [hright, Ne.symm hright, ite_false]
        exact hold

private theorem other_group_ports {l : PortLayout} (hl : l.pages.Valid) {port : ℕ}
    (groups : l.AxisGroups port) {g : Placement} (hg : g ∈ placements l)
    (hu : g ≠ groups.upper) (hlow : g ≠ groups.lower) : port ≠ g.left ∧ port ≠ g.right := by
  have houter (hk : port = g.left ∨ port = g.right) : False := by
    cases hs : g.side with
    | upper => exact hu (groups.upper_unique hl hg hs hk)
    | lower => exact hlow (groups.lower_outer_unique hl hg hs hk)
  exact ⟨fun h => houter (Or.inl h), fun h => houter (Or.inr h)⟩

/-- One interface-axis change updates only its two actual incident groups' canonical slots. -/
theorem canonical_axis_update (l : PortLayout) (hl : l.pages.Valid) (axes : List Bool)
    {port : ℕ} (hp : port < axes.length) (groups : l.AxisGroups port) (gain : Bool) :
    (⟨axes.set port gain,
      groups.lower.canonicalUpdate (groups.upper.canonicalUpdate (l.canonical axes).internal port gain) port gain⟩ : SignalState) =
      l.canonical (axes.set port gain) := by
  have hne : groups.upper ≠ groups.lower := by
    intro h
    have hs := groups.upper_side.symm.trans ((congrArg Placement.side h).trans groups.lower_side)
    cases hs
  apply l.canonical_ext (axes.set port gain) _ rfl
  · simp only [Placement.canonicalUpdate_length, l.canonical_internal_length]
  · intro g hg j hj
    by_cases hlow : g = groups.lower
    · subst g
      apply canonicalUpdate_own l hl groups.lower_mem axes _ (Placement.canonicalUpdate_length _ _ _ _) _ hp gain hj
      intro q hq
      exact canonicalUpdate_other l groups.upper_mem groups.lower_mem hne _ port gain hq
    · rw [canonicalUpdate_other l groups.lower_mem hg (Ne.symm hlow) _ port gain hj]
      by_cases hu : g = groups.upper
      · subst g
        exact canonicalUpdate_own l hl groups.upper_mem axes _ rfl (fun _ _ => rfl) hp gain hj
      · rw [canonicalUpdate_other l groups.upper_mem hg (Ne.symm hu) _ port gain hj]
        have hports := other_group_ports hl groups hg hu hlow
        exact l.canonical_slot_congr axes (axes.set port gain) hg hj
          (List.getD_set_ne hports.1).symm (fun _ => (List.getD_set_ne hports.2).symm)

end PushPuzzle.PushS.PortLayout
