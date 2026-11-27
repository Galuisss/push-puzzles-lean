/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortInputLegal
public import PushS.PortGateIndexing
import all PushS.PortLayoutPolyTime
import all PushS.PortGateIndexing
import all PushS.PortWireIndexing
import all PushS.PortSegments
import CslibFrontier.Foundations.Data.List.FlatMapPositions
import CslibFrontier.Foundations.Data.List.Lookup

/-! Exact reads and allocation bounds for the actual canonical signal arrays. -/

public section
namespace PushPuzzle.PushS.PortLayout


private theorem lowerSignals_length (axes : List Bool) (g : LowerGroup) :
    (lowerSignals axes g).length = g.internalCount := by cases g <;> rfl

private theorem lowerSignals_flatMap_length (axes : List Bool) (gs : List LowerGroup) :
    (gs.flatMap (lowerSignals axes)).length = (gs.map LowerGroup.internalCount).sum := by
  rw [List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro g _
  exact lowerSignals_length axes g

/-- Canonical physical internal arrays allocate exactly one slot per WIRE and three per gate. -/
theorem canonical_internal_length (l : PortLayout) (axes : List Bool) :
    (l.canonical axes).internal.length = l.upperPairs.length + (l.lowerGroups.map LowerGroup.internalCount).sum := by
  change ((_ ++ l.lowerGroups.flatMap (lowerSignals axes)) : List Bool).length = _
  rw [List.length_append, List.length_map, lowerSignals_flatMap_length]

private theorem lower_slot_bound (l : PortLayout) (axes : List Bool) (i : Fin l.lowerGroups.length)
    {j : ℕ} (hj : j < (l.lowerGroups.get i).internalCount) :
    l.lowerOffset i + j < (l.canonical axes).internal.length := by
  have hj' : j < (lowerSignals axes l.lowerGroups[i.val]).length := by
    simpa only [lowerSignals_length, List.get_eq_getElem] using hj
  have hb := List.flatMap_prefix_add_lt l.lowerGroups (lowerSignals axes) i.isLt hj'
  rw [lowerSignals_flatMap_length, lowerSignals_flatMap_length] at hb
  rw [l.canonical_internal_length axes]
  unfold lowerOffset
  omega

private theorem lower_slot_read (l : PortLayout) (axes : List Bool) (i : Fin l.lowerGroups.length)
    {j : ℕ} (hj : j < (l.lowerGroups.get i).internalCount) :
    (l.canonical axes).internal.getD (l.lowerOffset i + j) false =
      (lowerSignals axes (l.lowerGroups.get i)).getD j false := by
  have hj' : j < (lowerSignals axes l.lowerGroups[i.val]).length := by
    simpa only [lowerSignals_length, List.get_eq_getElem] using hj
  have hprefix := lowerSignals_flatMap_length axes (l.lowerGroups.take i.val)
  change ((_ ++ l.lowerGroups.flatMap (lowerSignals axes)) : List Bool).getD _ false = _
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_map, lowerOffset]; omega)]
  have hoff : l.lowerOffset i + j - l.upperPairs.length =
      ((l.lowerGroups.take i.val).flatMap (lowerSignals axes)).length + j := by
    rw [hprefix]
    unfold lowerOffset
    omega
  rw [List.length_map, hoff]
  rw [List.getD_eq_getElem _ _ (List.flatMap_prefix_add_lt l.lowerGroups (lowerSignals axes) i.isLt hj'),
    List.getElem_flatMap_prefix_add l.lowerGroups (lowerSignals axes) i.isLt hj']
  exact (List.getD_eq_getElem _ _ hj').symm

/-- The actual upper WIRE slot reads the complement of its left interface bit. -/
theorem canonical_upper_read (l : PortLayout) (axes : List Bool) (i : Fin l.upperPairs.length) :
    (l.canonical axes).internal.getD i false = !(axes.getD (l.upperPairs.get i).1 false) := by
  change ((_ ++ l.lowerGroups.flatMap (lowerSignals axes)) : List Bool).getD _ false = _
  rw [List.getD_append _ _ _ _ (by simpa only [List.length_map] using i.isLt)]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using i.isLt)]
  simp only [List.getElem_map, List.get_eq_getElem]

/-- The actual lower WIRE slot reads its left interface bit. -/
theorem canonical_lower_wire_read (l : PortLayout) (axes : List Bool) (i : Fin l.lowerGroups.length)
    (a b : ℕ) (hi : l.lowerGroups.get i = .wire a b) :
    (l.canonical axes).internal.getD (l.lowerOffset i) false = axes.getD a false := by
  have h := lower_slot_read l axes i (j := 0) (by simp only [hi, LowerGroup.internalCount]; decide +kernel)
  simpa only [Nat.add_zero, hi, lowerSignals, List.getD_cons_zero] using h

/-- The actual gate's three slots read its left interface bit and twice its lower heavy input. -/
theorem canonical_lower_gate_read (l : PortLayout) (axes : List Bool) (i : Fin l.lowerGroups.length)
    (kind : Shuttle.Kind) (first : ℕ) (hi : l.lowerGroups.get i = .gate kind first) :
    (l.canonical axes).internal.getD (l.lowerOffset i) false = axes.getD first false ∧
      (l.canonical axes).internal.getD (l.lowerOffset i + 1) false = !(axes.getD (first + 2) false) ∧
      (l.canonical axes).internal.getD (l.lowerOffset i + 2) false = !(axes.getD (first + 2) false) := by
  have h0 := lower_slot_read l axes i (j := 0) (by simp only [hi, LowerGroup.internalCount]; decide +kernel)
  have h1 := lower_slot_read l axes i (j := 1) (by simp only [hi, LowerGroup.internalCount]; decide +kernel)
  have h2 := lower_slot_read l axes i (j := 2) (by simp only [hi, LowerGroup.internalCount]; decide +kernel)
  simpa only [Nat.add_zero, hi, lowerSignals, List.getD_cons_zero, List.getD_cons_succ] using And.intro h0 (And.intro h1 h2)

private theorem lower_at_zipIdx (l : PortLayout) {g : LowerGroup} {i : ℕ}
    (hi : (g, i) ∈ l.lowerGroups.zipIdx) :
    l.lowerGroups.get ⟨i, by simpa using List.snd_lt_of_mem_zipIdx hi⟩ = g := by
  have h := List.fst_eq_of_mem_zipIdx hi
  simp only [Nat.sub_zero] at h
  exact h.symm

/-- Every actually emitted group receives all of its canonical internal slots. -/
theorem canonical_placement_bounds (l : PortLayout) (axes : List Bool) {g : Placement}
    (hg : g ∈ placements l) :
    g.internal + (if g.gate.isSome then 3 else 1) ≤ (l.canonical axes).internal.length := by
  simp only [placements, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨⟨⟨a, b⟩, i⟩, hi, rfl⟩ | ⟨⟨lower, i⟩, hi, rfl⟩
  · have hb := List.snd_lt_of_mem_zipIdx hi
    rw [l.canonical_internal_length axes]
    change i + 1 ≤ _
    omega
  · let j : Fin l.lowerGroups.length := ⟨i, by simpa using List.snd_lt_of_mem_zipIdx hi⟩
    have hj : l.lowerGroups.get j = lower := lower_at_zipIdx l hi
    cases lower with
    | wire a b =>
      have hb := lower_slot_bound l axes j (j := 0) (by simp only [hj, LowerGroup.internalCount]; decide +kernel)
      change l.lowerOffset i + 0 < _ at hb
      change l.lowerOffset i + 1 ≤ _
      omega
    | gate kind first =>
      have hb := lower_slot_bound l axes j (j := 2) (by simp only [hj, LowerGroup.internalCount]; decide +kernel)
      change l.lowerOffset i + 2 < _ at hb
      change l.lowerOffset i + 3 ≤ _
      omega

/-- Each actually emitted ordinary WIRE reads its own canonical signal. -/
theorem canonical_wire_read (l : PortLayout) (axes : List Bool) {g : Placement}
    (hg : g ∈ placements l) (hw : g.gate = none) :
    (l.canonical axes).internal.getD g.internal false =
      (if g.side = .upper then !(axes.getD g.left false) else axes.getD g.left false) := by
  simp only [placements, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨⟨⟨a, b⟩, i⟩, hi, rfl⟩ | ⟨⟨lower, i⟩, hi, rfl⟩
  · let j : Fin l.upperPairs.length := ⟨i, by simpa using List.snd_lt_of_mem_zipIdx hi⟩
    have hread : l.upperPairs.get j = (a, b) := by
      have h := List.fst_eq_of_mem_zipIdx hi
      simp only [Nat.sub_zero] at h
      exact h.symm
    simpa only [hread, ite_true] using l.canonical_upper_read axes j
  · let j : Fin l.lowerGroups.length := ⟨i, by simpa using List.snd_lt_of_mem_zipIdx hi⟩
    cases lower with
    | wire a b =>
      have h := l.canonical_lower_wire_read axes j a b (lower_at_zipIdx l hi)
      simpa only [encLowerGroup_elim, encLowerGroup_toSum, Sum.elim_inl, reduceCtorEq, ite_false] using h
    | gate kind first => simp [encLowerGroup_elim, encLowerGroup_toSum] at hw

/-- The three actual gate slots read the actual left interface and twice its heavy input. -/
theorem canonical_gate_read (l : PortLayout) (axes : List Bool) {g : Placement}
    (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    (l.canonical axes).internal.getD g.internal false = axes.getD g.left false ∧
      (l.canonical axes).internal.getD (g.internal + 1) false = !(axes.getD g.right false) ∧
      (l.canonical axes).internal.getD (g.internal + 2) false = !(axes.getD g.right false) := by
  simp only [placements, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨⟨⟨a, b⟩, i⟩, hi, rfl⟩ | ⟨⟨lower, i⟩, hi, rfl⟩
  · cases hk
  · let j : Fin l.lowerGroups.length := ⟨i, by simpa using List.snd_lt_of_mem_zipIdx hi⟩
    cases lower with
    | wire a b => simp [encLowerGroup_elim, encLowerGroup_toSum] at hk
    | gate other first =>
      simpa only [encLowerGroup_elim, encLowerGroup_toSum, Sum.elim_inr] using
        l.canonical_lower_gate_read axes j other first (lower_at_zipIdx l hi)

/-- The actual ordinary group's two interface inputs satisfy its native page threshold. -/
theorem InputLegal.wire_inputs {l : PortLayout} {axes : List Bool} (h : l.InputLegal axes)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) :
    if g.side = .upper then axes.getD g.left false = true ∨ axes.getD g.right false = true
    else axes.getD g.left false = false ∨ axes.getD g.right false = false := by
  simp only [placements, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨⟨⟨a, b⟩, i⟩, hi, rfl⟩ | ⟨⟨lower, i⟩, hi, rfl⟩
  · exact h.upper a b (List.fst_mem_of_mem_zipIdx hi)
  · cases lower with
    | wire a b =>
      simpa only [encLowerGroup_elim, encLowerGroup_toSum, Sum.elim_inl, reduceCtorEq, ite_false] using
        h.lower_wire a b (List.fst_mem_of_mem_zipIdx hi)
    | gate kind first => simp [encLowerGroup_elim, encLowerGroup_toSum] at hw

/-- The actual gate's interface bits satisfy the corresponding AND/OR threshold. -/
theorem InputLegal.gate_inputs {l : PortLayout} {axes : List Bool} (h : l.InputLegal axes)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    if kind = .andGate then axes.getD g.right false = false ∨
        (axes.getD g.left false = false ∧ axes.getD (g.left + 1) false = false)
    else axes.getD g.left false = false ∨ axes.getD (g.left + 1) false = false ∨ axes.getD g.right false = false := by
  have hs := placement_gate_shape l hg hk
  cases kind with
  | andGate =>
    simpa only [hs.2, ite_true] using h.and_gate g.left (placement_gate_mem l hg hk)
  | orGate =>
    simpa only [hs.2, reduceCtorEq, ite_false] using h.or_gate g.left (placement_gate_mem l hg hk)

/-- The actual AND group's middle lower input is ordered below its left lower input. -/
theorem OrderedInputs.gate_order {l : PortLayout} {axes : List Bool} (h : l.OrderedInputs axes)
    {g : Placement} (hg : g ∈ placements l) (hk : g.gate = some .andGate) :
    axes.getD (g.left + 1) false = false → axes.getD g.left false = false :=
  h.and_ordered g.left (placement_gate_mem l hg hk)

end PushPuzzle.PushS.PortLayout
