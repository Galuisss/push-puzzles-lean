/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortAxisMacro
import all PushS.PortEndpointIndexing
import all PushS.PortEndpointCounts
import all PushS.PortSegments

/-! Actual group owners and working-level ordering along a horizontal WIRE. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PageLevels

private def pageFor (l : PortLayout) : Side → Page
  | .upper => l.pages.upperPage
  | .lower => l.pages.lowerPage

private def levelFor (l : PortLayout) : (side : Side) → (pageFor l side).Index → ℕ
  | .upper => l.pages.upperLevel
  | .lower => l.pages.lowerLevel

private theorem pageFor_valid (l : PortLayout) (hl : l.pages.Valid) (side : Side) :
    (pageFor l side).Valid := by
  cases side
  · exact hl.upper
  · exact hl.lower

private theorem upperLevel_index (l : PortLayout) (i : Fin l.upperPairs.length) :
    l.upperLevel i = l.pages.upperLevel ⟨i.val, by simpa only [pages, Pages.upperPage, Pages.lowerPage, List.length_map] using i.isLt⟩ := by
  unfold upperLevel
  rw [List.getD_eq_getElem _ _ (by
    change i.val < (List.ofFn l.pages.upperLevel).length
    rw [List.length_ofFn]
    simpa only [pages, Pages.upperPage, Pages.lowerPage, List.length_map] using i.isLt)]
  simp only [Pages.levels, List.getElem_ofFn]

private theorem lowerLevel_index (l : PortLayout) (i : Fin l.lowerGroups.length) :
    l.lowerLevel i = l.pages.lowerLevel ⟨i.val, by simpa only [pages, Pages.upperPage, Pages.lowerPage, List.length_map] using i.isLt⟩ := by
  unfold lowerLevel
  rw [List.getD_eq_getElem _ _ (by
    change i.val < (List.ofFn l.pages.lowerLevel).length
    rw [List.length_ofFn]
    simpa only [pages, Pages.upperPage, Pages.lowerPage, List.length_map] using i.isLt)]
  simp only [Pages.levels, List.getElem_ofFn]

private theorem wire_owner (l : PortLayout) {g : Placement}
    (hg : g ∈ placements l) (hw : g.gate = none) :
    ∃ i : (pageFor l g.side).Index,
      (pageFor l g.side).group i = .wire g.left g.right ∧ levelFor l g.side i = g.level := by
  simp only [placements, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨⟨⟨a, b⟩, k⟩, hk, rfl⟩ | ⟨⟨lower, k⟩, hk, rfl⟩
  · let i : Fin l.upperPairs.length := ⟨k, by simpa using List.snd_lt_of_mem_zipIdx hk⟩
    refine ⟨⟨i.val, by simpa only [pageFor, pages, Pages.upperPage, Pages.lowerPage, List.length_map] using i.isLt⟩, upper_group_at l hk, ?_⟩
    exact (upperLevel_index l i).symm
  · cases lower with
    | wire a b =>
      simp only [encLowerGroup_elim, encLowerGroup_toSum, Sum.elim_inl]
      let i : Fin l.lowerGroups.length := ⟨k, by simpa using List.snd_lt_of_mem_zipIdx hk⟩
      refine ⟨⟨i.val, by simpa only [pageFor, pages, Pages.upperPage, Pages.lowerPage, List.length_map] using i.isLt⟩, lower_group_at l hk, ?_⟩
      exact (lowerLevel_index l i).symm
    | gate kind first => simp [encLowerGroup_elim, encLowerGroup_toSum] at hw

private theorem endpoint_owner (l : PortLayout) (hl : l.pages.Valid) {e : Endpoint}
    (he : e ∈ l.endpoints) :
    ∃ i : (pageFor l e.side).Index,
      e.port ∈ ((pageFor l e.side).group i).ports ∧
      (e.port = ((pageFor l e.side).group i).left ∨
        e.port = ((pageFor l e.side).group i).right) ∧
      levelFor l e.side i = e.level := by
  cases hs : e.side with
  | upper =>
    obtain ⟨i, hi, hout, _, hlevel, _⟩ := upper_endpoint_owner l hl he hs
    refine ⟨i, hi, hout, ?_⟩
    exact (upperLevel_index l ⟨i.val, by simpa only [pages, Pages.upperPage, Pages.lowerPage, List.length_map] using i.isLt⟩).symm.trans hlevel.symm
  | lower =>
    obtain ⟨i, hi, hout, _, hlevel, _⟩ := lower_endpoint_owner l hl he hs
    refine ⟨i, hi, hout, ?_⟩
    exact (lowerLevel_index l ⟨i.val, by simpa only [pages, Pages.upperPage, Pages.lowerPage, List.length_map] using i.isLt⟩).symm.trans hlevel.symm

private theorem levelFor_parent_gt (l : PortLayout) (hl : l.pages.Valid) (side : Side)
    {i j : (pageFor l side).Index}
    (hc : ((pageFor l side).group i).Contains ((pageFor l side).group j)) :
    levelFor l side j < levelFor l side i := by
  cases side
  · exact Pages.upperLevel_parent_gt hl hc
  · exact Pages.lowerLevel_parent_gt hl hc

private theorem contains_of_outer_port_inside (page : Page) (hp : page.Valid)
    (i j : page.Index) {a b k : ℕ} (hi : page.group i = .wire a b)
    (hk : k = (page.group j).left ∨ k = (page.group j).right)
    (ha : a < k) (hb : k < b) : (page.group i).Contains (page.group j) := by
  have hij : i ≠ j := by intro h; subst j; simp [hi, Group.left, Group.right] at hk; omega
  have hbounds := hp.bounded j
  rcases hp.noncrossing i j hij with h | h | h | h
  · rw [hi] at h
    change b < (page.group j).left at h; omega
  · rw [hi] at h
    change (page.group j).right < a at h; omega
  · exact h
  · have hc := h
    rw [hi] at hc
    change (page.group j).left ≤ a ∧ b ≤ (page.group j).right ∧ _ at hc
    omega

private theorem interior_endpoint_shallower (l : PortLayout) (hl : l.pages.Valid)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {e : Endpoint} (he : e ∈ l.endpoints) (hs : e.side = g.side)
    (ha : g.left < e.port) (hb : e.port < g.right) : e.level < g.level := by
  obtain ⟨i, hi, hgi⟩ := wire_owner l hg hw
  have ho := endpoint_owner l hl he
  rw [hs] at ho
  obtain ⟨j, _, hout, hej⟩ := ho
  have hc := contains_of_outer_port_inside _ (pageFor_valid l hl g.side) i j hi hout ha hb
  have hlt := levelFor_parent_gt l hl g.side hc
  simpa only [hgi, hej] using hlt

private theorem prefix_sum_mono (xs : List ℕ) {i j : ℕ} (hij : i ≤ j) :
    (xs.take i).sum ≤ (xs.take j).sum := by
  induction xs generalizing i j with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [List.take_succ_cons, List.sum_cons]
        exact Nat.add_le_add_left (ih (by omega)) x

private theorem lowerOffset_before (l : PortLayout) {g : LowerGroup} {i j : ℕ}
    (hi : (g, i) ∈ l.lowerGroups.zipIdx) (hij : i < j) :
    l.lowerOffset i + g.internalCount ≤ l.lowerOffset j := by
  have hread := List.fst_eq_of_mem_zipIdx hi
  simp only [Nat.sub_zero] at hread
  have hstep : ((l.lowerGroups.take (i + 1)).map LowerGroup.internalCount).sum =
      ((l.lowerGroups.take i).map LowerGroup.internalCount).sum + g.internalCount := by
    rw [List.take_succ_eq_append_getElem (List.snd_lt_of_mem_zipIdx hi),
      List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, hread]
  have hm := prefix_sum_mono (l.lowerGroups.map LowerGroup.internalCount)
    (i := i + 1) (j := j) (by omega)
  simp only [← List.map_take, hstep] at hm
  unfold lowerOffset
  omega

private theorem zipIdx_unique {α : Type} {xs : List α} {a b : α} {i : ℕ}
    (ha : (a, i) ∈ xs.zipIdx) (hb : (b, i) ∈ xs.zipIdx) : a = b :=
  Option.some.inj ((List.mem_zipIdx_iff_getElem?.mp ha).symm.trans
    (List.mem_zipIdx_iff_getElem?.mp hb))

private def slotCount (g : Placement) : ℕ := if g.gate.isSome then 3 else 1

private theorem first_slot_owner (l : PortLayout) {g h : Placement}
    (hg : g ∈ placements l) (hh : h ∈ placements l)
    (hle : g.internal ≤ h.internal) (hlt : h.internal < g.internal + slotCount g) : g = h := by
  simp only [placements, List.mem_append, List.mem_map] at hg hh
  rcases hg with ⟨⟨⟨a, b⟩, i⟩, hi, rfl⟩ | ⟨⟨lower, i⟩, hi, rfl⟩
  · rcases hh with ⟨⟨⟨c, d⟩, j⟩, hj, rfl⟩ | ⟨⟨lower, j⟩, hj, rfl⟩
    · have hij : i = j := by
        change i ≤ j at hle
        change j < i + 1 at hlt
        omega
      subst j
      have heq := zipIdx_unique hi hj
      cases heq
      rfl
    · have hub := List.snd_lt_of_mem_zipIdx hi
      have hlo : l.upperPairs.length ≤ l.lowerOffset j := by unfold lowerOffset; omega
      cases lower <;> change l.lowerOffset j < i + 1 at hlt <;> omega
  · rcases hh with ⟨⟨⟨a, b⟩, j⟩, hj, rfl⟩ | ⟨⟨other, j⟩, hj, rfl⟩
    · have hub := List.snd_lt_of_mem_zipIdx hj
      have hlo : l.upperPairs.length ≤ l.lowerOffset i := by unfold lowerOffset; omega
      cases lower <;> simp only [encLowerGroup_elim, encLowerGroup_toSum,
        Sum.elim_inl, Sum.elim_inr] at hle <;> omega
    · rcases lt_trichotomy i j with hij | hij | hij
      · have hb := lowerOffset_before l hi hij
        cases lower <;> cases other <;> simp only [encLowerGroup_elim, encLowerGroup_toSum,
          Sum.elim_inl, Sum.elim_inr, slotCount, Option.isSome_none, Option.isSome_some,
          Bool.false_eq_true, ite_false, ite_true, LowerGroup.internalCount] at hlt hb <;> omega
      · subst j
        have heq := zipIdx_unique hi hj
        cases heq
        rfl
      · have hb := lowerOffset_before l hj hij
        cases lower <;> cases other <;> simp only [encLowerGroup_elim, encLowerGroup_toSum,
          Sum.elim_inl, Sum.elim_inr, LowerGroup.internalCount] at hle hb <;> omega

private def wireLeft (g : Placement) : Endpoint :=
  ⟨g.side, g.left, true, g.level, g.internal⟩

private def wireRight (g : Placement) : Endpoint :=
  ⟨g.side, g.right, false, g.level, g.internal⟩

private theorem wire_endpoints (l : PortLayout) {g : Placement}
    (hg : g ∈ placements l) (hw : g.gate = none) :
    wireLeft g ∈ l.endpoints ∧ wireRight g ∈ l.endpoints := by
  constructor
  · exact List.mem_flatMap.mpr ⟨g, hg, List.mem_cons_self⟩
  · apply List.mem_flatMap.mpr
    refine ⟨g, hg, ?_⟩
    simp [wireRight, hw]

private theorem wire_ports (l : PortLayout) (hl : l.pages.Valid) {g : Placement}
    (hg : g ∈ placements l) (hw : g.gate = none) : g.left < g.right ∧ g.right < l.portCount := by
  obtain ⟨i, hi, _⟩ := wire_owner l hg hw
  have hb := (pageFor_valid l hl g.side).bounded i
  have hc : (pageFor l g.side).portCount = l.portCount := by cases g.side <;> rfl
  simpa only [hi, Group.left, Group.right, hc] using hb

private theorem endpoint_slot (g : Placement) {e : Endpoint}
    (he : e ∈ [⟨g.side, g.left, true, g.level, g.internal⟩,
      ⟨g.side, g.right, false, g.level, g.internal + if g.gate.isSome then 2 else 0⟩]) :
    g.internal ≤ e.internal ∧ e.internal < g.internal + slotCount g := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  all_goals cases hg : g.gate <;>
    simp only [slotCount, hg, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
      ite_false, ite_true] <;> omega

private theorem wire_endpoint_internal (l : PortLayout) {g : Placement}
    (hg : g ∈ placements l) (hw : g.gate = none) {e : Endpoint}
    (he : e ∈ l.endpoints) (hneL : e ≠ wireLeft g) (hneR : e ≠ wireRight g) :
    e.internal ≠ g.internal := by
  intro hi
  obtain ⟨h, hh, hend⟩ := List.mem_flatMap.mp he
  have hb := endpoint_slot h hend
  rw [hi] at hb
  have heq := first_slot_owner l hh hg hb.1 hb.2
  subst h
  simp only [hw, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero,
    List.mem_cons, List.not_mem_nil, or_false] at hend
  exact hend.elim hneL hneR

private theorem wire_core_internal (l : PortLayout) {g h : Placement}
    (hg : g ∈ placements l) (hw : g.gate = none) (hh : h ∈ placements l)
    {kind : Shuttle.Kind} (hcore : h.gate = some kind) {j : ℕ} (hj : j < 3) :
    h.internal + j ≠ g.internal := by
  intro hi
  have heq : h = g := first_slot_owner l hh hg (by omega) (by
    simp only [slotCount, hcore, Option.isSome_some, ite_true]
    omega)
  have hc := congrArg Placement.gate heq
  rw [hcore, hw] at hc
  cases hc

end PushPuzzle.PushS.PortLayout
