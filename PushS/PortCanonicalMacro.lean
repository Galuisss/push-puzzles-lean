/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortCanonicalAxisMacro
public import PushS.PortCanonicalGroupMacro
import all PushS.PortCanonicalUpdate
import all PushS.PortGateIndexing
import all PushS.PortWireIndexing
import all PushS.PortSegments

/-! Actual canonical-to-canonical single-axis flips on the complete marked wall-free board. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction

private theorem canonicalUpdate_set_comm (g : Placement) (bits : List Bool) (port : ℕ) (gain : Bool)
    (i : ℕ) (value : Bool)
    (hindex : ∀ j < (if g.gate.isSome then 3 else 1), g.internal + j ≠ i) :
    g.canonicalUpdate (bits.set i value) port gain = (g.canonicalUpdate bits port gain).set i value := by
  by_cases hleft : g.left = port
  · simp only [Placement.canonicalUpdate, hleft, ite_true]
    exact List.set_comm _ _ (by have h := hindex 0 (by split <;> omega); simp only [Nat.add_zero] at h; exact Ne.symm h)
  · simp only [Placement.canonicalUpdate, hleft, ite_false]
    by_cases hheavy : g.gate.isSome = true ∧ g.right = port
    · simp only [hheavy, and_self, ite_true]
      have h1 := hindex 1 (by simp only [hheavy.1, ite_true]; omega)
      have h2 := hindex 2 (by simp only [hheavy.1, ite_true]; omega)
      rw [List.set_comm value (!gain) (Ne.symm h1), List.set_comm value (!gain) (Ne.symm h2)]
    · simp only [hheavy, ite_false]

private theorem canonicalUpdate_comm (l : PortLayout) {g h : Placement}
    (hg : g ∈ placements l) (hh : h ∈ placements l) (hne : g ≠ h)
    (bits : List Bool) (port : ℕ) (gain : Bool) :
    g.canonicalUpdate (h.canonicalUpdate bits port gain) port gain =
      h.canonicalUpdate (g.canonicalUpdate bits port gain) port gain := by
  have hindex {i : ℕ} (hi : i < (if h.gate.isSome then 3 else 1)) :
      ∀ j < (if g.gate.isSome then 3 else 1), g.internal + j ≠ h.internal + i := by
    intro j hj heq
    apply hne
    apply placement_slot_overlap l hg hh (k := g.internal + j)
    · change g.internal ≤ g.internal + j ∧ g.internal + j < g.internal + (if g.gate.isSome then 3 else 1)
      omega
    · change h.internal ≤ g.internal + j ∧ g.internal + j < h.internal + (if h.gate.isSome then 3 else 1)
      omega
  change g.canonicalUpdate (if h.left = port then bits.set h.internal (if h.side = .upper then !gain else gain)
    else if h.gate.isSome = true ∧ h.right = port then (bits.set (h.internal + 1) (!gain)).set (h.internal + 2) (!gain)
    else bits) port gain =
    (if h.left = port then (g.canonicalUpdate bits port gain).set h.internal (if h.side = .upper then !gain else gain)
    else if h.gate.isSome = true ∧ h.right = port then ((g.canonicalUpdate bits port gain).set (h.internal + 1) (!gain)).set (h.internal + 2) (!gain)
    else g.canonicalUpdate bits port gain)
  by_cases hleft : h.left = port
  · simp only [hleft, ite_true]
    exact canonicalUpdate_set_comm g bits port gain h.internal _ (by simpa only [Nat.add_zero] using hindex (i := 0) (by split <;> omega))
  · simp only [hleft, ite_false]
    by_cases hheavy : h.gate.isSome = true ∧ h.right = port
    · simp only [hheavy, and_self, ite_true]
      rw [canonicalUpdate_set_comm g _ port gain (h.internal + 2) _ (hindex (i := 2) (by simp only [hheavy.1, ite_true]; omega)),
        canonicalUpdate_set_comm g _ port gain (h.internal + 1) _ (hindex (i := 1) (by simp only [hheavy.1, ite_true]; omega))]
    · simp only [hheavy, ite_false]

private theorem groups_sides_ne {l : PortLayout} {port : ℕ} (groups : l.AxisGroups port) :
    groups.upper ≠ groups.lower := by
  intro h
  have hs := groups.upper_side.symm.trans ((congrArg Placement.side h).trans groups.lower_side)
  cases hs

/-- Every ordered legal single-axis change has a genuine complete-board canonical frame-to-frame run. -/
theorem encodedSegments_canonical_axis_from_frame (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (axes : List Bool) (hlegal : l.InputLegal axes) {port : ℕ} (hp : port < l.portCount)
    (gain : Bool) (hbefore : axes.getD port false = !gain) (hnew : l.OrderedInputs (axes.set port gain))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Reachable B none (l.cornerState p (l.canonical axes)).toState
      (l.cornerState p (l.canonical (axes.set port gain))).toState := by
  obtain ⟨groups⟩ := l.axisGroups_nonempty hl hp
  have hpa : port < axes.length := by simpa only [hlegal.axes_length] using hp
  let losing := if gain then groups.lower else groups.upper
  let gaining := if gain then groups.upper else groups.lower
  have hlosing : losing ∈ placements l := by cases gain <;> first | exact groups.upper_mem | exact groups.lower_mem
  have hgaining : gaining ∈ placements l := by cases gain <;> first | exact groups.upper_mem | exact groups.lower_mem
  have hne : losing ≠ gaining := by cases gain <;> first | exact groups_sides_ne groups | exact Ne.symm (groups_sides_ne groups)
  have hprep := l.encodedSegments_canonical_group_from_frame p hl hM ha axes hlegal (l.canonical axes) hlosing gain hbefore
    (by cases gain <;> simp only [losing, Bool.false_eq_true, ite_false, ite_true, groups.upper_side, groups.lower_side, reduceCtorEq,
      show (l.canonical axes).axes = axes from rfl])
    rfl (fun _ _ => rfl) B hB
  change Reachable B none (l.cornerState p (l.canonical axes)).toState (l.cornerState p (groups.prepared axes gain)).toState at hprep
  have haxis := l.encodedSegments_prepared_axis_from_frame p hl hM ha axes hlegal hpa groups gain hbefore hnew B hB
  let switched := {groups.prepared axes gain with axes := axes.set port gain}
  have hpost := l.encodedSegments_canonical_group_from_frame p hl hM ha axes hlegal switched hgaining gain hbefore
    (by cases gain <;> simp only [switched, gaining, Bool.false_eq_true, ite_false, ite_true, groups.upper_side, groups.lower_side, reduceCtorEq])
    (Placement.canonicalUpdate_length losing _ port gain)
    (by intro j hj; exact canonicalUpdate_other l hlosing hgaining hne _ port gain hj) B hB
  have hfinal : {switched with internal := gaining.canonicalUpdate switched.internal port gain} = l.canonical (axes.set port gain) := by
    cases gain
    · exact l.canonical_axis_update hl axes hpa groups false
    · change (⟨axes.set port true, groups.upper.canonicalUpdate (groups.lower.canonicalUpdate (l.canonical axes).internal port true) port true⟩ : SignalState) = _
      rw [canonicalUpdate_comm l groups.upper_mem groups.lower_mem (groups_sides_ne groups)]
      exact l.canonical_axis_update hl axes hpa groups true
  rw [hfinal] at hpost
  exact hprep.trans (haxis.trans hpost)

end PushPuzzle.PushS.PortLayout
