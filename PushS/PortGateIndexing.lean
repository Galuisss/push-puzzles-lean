/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortWireIndexing
import all PushS.PortWireIndexing
import all PushS.PortCoreCrossing
import all PushS.PortSegmentBounds
import all PushS.PortSegments

/-! The actual middle internal slot belongs only to its three-port short train. -/

namespace PushPuzzle.PushS.PortLayout


private theorem gate_level_one (l : PortLayout) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) : g.level = 1 := by
  simp only [placements, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨⟨⟨a, b⟩, i⟩, hi, rfl⟩ | ⟨⟨lower, i⟩, hi, rfl⟩
  · cases hk
  · cases lower with
    | wire a b => simp [encLowerGroup_elim, encLowerGroup_toSum] at hk
    | gate other first =>
      let j : Fin l.lowerGroups.length := ⟨i, by simpa using List.snd_lt_of_mem_zipIdx hi⟩
      exact (lowerLevel_index l j).trans (l.pages.lowerLevel_triple (lower_group_at l hi))

private theorem gate_port_bounds (l : PortLayout) (hl : l.pages.Valid) {g : Placement}
    (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    g.left < g.right ∧ g.right < l.portCount := by
  have hs := placement_gate_shape l hg hk
  have hb := group_mem_bound l.pages.lowerPage hl.lower
    (List.mem_map.mpr ⟨LowerGroup.gate kind g.left, placement_gate_mem l hg hk, rfl⟩)
  change g.left < g.left + 2 ∧ g.left + 2 < l.portCount at hb
  simpa only [hs.2] using hb

private theorem placement_slot_overlap (l : PortLayout) {g h : Placement}
    (hg : g ∈ placements l) (hh : h ∈ placements l) {k : ℕ}
    (hkg : g.internal ≤ k ∧ k < g.internal + slotCount g)
    (hkh : h.internal ≤ k ∧ k < h.internal + slotCount h) : g = h := by
  rcases le_total g.internal h.internal with hle | hle
  · exact first_slot_owner l hg hh hle (by omega)
  · exact (first_slot_owner l hh hg hle (by omega)).symm

private def gateLeft (g : Placement) : Endpoint :=
  ⟨g.side, g.left, true, g.level, g.internal⟩

private def gateRight (g : Placement) : Endpoint :=
  ⟨g.side, g.right, false, g.level, g.internal + 2⟩

private theorem gate_endpoints (l : PortLayout) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    gateLeft g ∈ l.endpoints ∧ gateRight g ∈ l.endpoints := by
  constructor
  · exact List.mem_flatMap.mpr ⟨g, hg, List.mem_cons_self⟩
  · apply List.mem_flatMap.mpr ⟨g, hg, ?_⟩
    simp only [hk, Option.isSome_some, ite_true]
    exact List.mem_cons_of_mem _ List.mem_cons_self

private theorem gate_endpoint_of_internal (l : PortLayout) {g : Placement}
    (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {e : Endpoint} (he : e ∈ l.endpoints)
    (hlo : g.internal ≤ e.internal) (hhi : e.internal < g.internal + 3) :
    e = gateLeft g ∨ e = gateRight g := by
  obtain ⟨h, hh, he⟩ := List.mem_flatMap.mp he
  have heq : h = g := placement_slot_overlap l hh hg (endpoint_slot h he) (by
    simp only [slotCount, hk, Option.isSome_some, ite_true]
    exact ⟨hlo, hhi⟩)
  subst h
  simpa only [hk, Option.isSome_some, ite_true, List.mem_cons, List.not_mem_nil, or_false,
    gateLeft, gateRight] using he

private theorem gate_short_endpoint_internal (l : PortLayout) {g : Placement}
    (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {e : Endpoint} (he : e ∈ l.endpoints) : e.internal ≠ g.internal + 1 := by
  intro hi
  obtain ⟨h, hh, he⟩ := List.mem_flatMap.mp he
  have heq : h = g := placement_slot_overlap l hh hg (endpoint_slot h he) (by
    rw [hi]
    simp only [slotCount, hk, Option.isSome_some, ite_true]
    omega)
  subst h
  simp only [hk, Option.isSome_some, ite_true, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> dsimp only at hi <;> omega

private theorem gate_other_internal (l : PortLayout) {g h : Placement}
    (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (hh : h ∈ placements l) {other : Shuttle.Kind} (hhk : h.gate = some other)
    (hne : h.internal ≠ g.internal) {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    h.internal + j ≠ g.internal + i := by
  intro he
  have hsame : h = g := placement_slot_overlap l hh hg (k := h.internal + j) (by
    simp only [slotCount, hhk, Option.isSome_some, ite_true]
    omega) (by
      simp only [slotCount, hk, Option.isSome_some, ite_true]
      omega)
  exact hne (congrArg Placement.internal hsame)

end PushPuzzle.PushS.PortLayout
