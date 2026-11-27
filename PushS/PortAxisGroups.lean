/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateIndexing
public import PushS.PortEndpointEnumeration
import all PushS.PortGateIndexing
import all PushS.PortWireIndexing
import all PushS.PortCoreCrossing
import all PushS.PortSegments

/-! The actual upper and lower group incident to one interface axis. -/

public section
namespace PushPuzzle.PushS.PortLayout


/-- The two actual emitted groups meeting one port, including a possible lower middle input. -/
structure AxisGroups (l : PortLayout) (port : ℕ) where
  /-- The actual upper ordinary group. -/
  upper : Placement
  /-- The upper group occurs in the emitter. -/
  upper_mem : upper ∈ placements l
  /-- The group occupies the upper page. -/
  upper_side : upper.side = .upper
  /-- Every upper group is ordinary. -/
  upper_wire : upper.gate = none
  /-- This port is one of its two ordinary endpoints. -/
  upper_port : port = upper.left ∨ port = upper.right
  /-- The actual lower group. -/
  lower : Placement
  /-- The lower group occurs in the emitter. -/
  lower_mem : lower ∈ placements l
  /-- The group occupies the lower page. -/
  lower_side : lower.side = .lower
  /-- This port is an outer endpoint or the middle input of a three-port group. -/
  lower_port : port = lower.left ∨ port = lower.right ∨
    (lower.gate.isSome = true ∧ port = lower.left + 1)

private theorem placement_outer_endpoint (l : PortLayout) {g : Placement}
    (hg : g ∈ placements l) {k : ℕ} (hk : k = g.left ∨ k = g.right) :
    ∃ e ∈ l.endpoints, e.side = g.side ∧ e.port = k ∧
      g.internal ≤ e.internal ∧ e.internal < g.internal + slotCount g := by
  have hs (e : Endpoint) (he : e ∈ [⟨g.side, g.left, true, g.level, g.internal⟩,
      ⟨g.side, g.right, false, g.level, g.internal + if g.gate.isSome then 2 else 0⟩]) :=
    endpoint_slot g he
  rcases hk with rfl | rfl
  · exact ⟨_, (placement_endpoints l hg).1, rfl, rfl, hs _ List.mem_cons_self⟩
  · exact ⟨_, (placement_endpoints l hg).2, rfl, rfl, hs _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

private theorem outer_group_owner (l : PortLayout) (hl : l.pages.Valid) {g h : Placement}
    (hg : g ∈ placements l) (hh : h ∈ placements l) (hs : g.side = h.side) {k : ℕ}
    (hkg : k = g.left ∨ k = g.right) (hkh : k = h.left ∨ k = h.right) : g = h := by
  obtain ⟨e, he, hes, hep, hei⟩ := placement_outer_endpoint l hg hkg
  obtain ⟨f, hf, hfs, hfp, hfi⟩ := placement_outer_endpoint l hh hkh
  have hef := l.endpoints_key_injective hl he hf (hes.trans (hs.trans hfs.symm)) (hep.trans hfp.symm)
  have hi := congrArg Endpoint.internal hef
  apply placement_slot_overlap l hg hh hei
  simpa only [hi] using hfi

private theorem incident_outer_owner (l : PortLayout) (hl : l.pages.Valid) {g h : Placement}
    (hg : g ∈ placements l) (hh : h ∈ placements l) (hs : g.side = h.side) {k : ℕ}
    (hkg : k = g.left ∨ k = g.right ∨ (g.gate.isSome = true ∧ k = g.left + 1))
    (hkh : k = h.left ∨ k = h.right) : g = h := by
  rcases hkg with hleft | hright | ⟨hgate, hmid⟩
  · exact outer_group_owner l hl hg hh hs (Or.inl hleft) hkh
  · exact outer_group_owner l hl hg hh hs (Or.inr hright) hkh
  · cases hk : g.gate with
    | none => simp only [hk, Option.isSome_none, Bool.false_eq_true] at hgate
    | some kind =>
      obtain ⟨e, he, hes, hep, _⟩ := placement_outer_endpoint l hh hkh
      have hsl := (placement_gate_shape l hg hk).1
      exact False.elim (l.endpoints_lower_ne_gate_middle hl (placement_gate_mem l hg hk) he
        (hes.trans (hs.symm.trans hsl)) (hep.trans hmid))

/-- The selected upper group owns every upper outer endpoint at this axis. -/
theorem AxisGroups.upper_unique {l : PortLayout} {k : ℕ} (groups : l.AxisGroups k)
    (hl : l.pages.Valid) {g : Placement} (hg : g ∈ placements l) (hs : g.side = .upper)
    (hk : k = g.left ∨ k = g.right) : g = groups.upper :=
  outer_group_owner l hl hg groups.upper_mem (hs.trans groups.upper_side.symm) hk groups.upper_port

/-- The selected lower group owns every lower outer endpoint at this axis. -/
theorem AxisGroups.lower_outer_unique {l : PortLayout} {k : ℕ} (groups : l.AxisGroups k)
    (hl : l.pages.Valid) {g : Placement} (hg : g ∈ placements l) (hs : g.side = .lower)
    (hk : k = g.left ∨ k = g.right) : g = groups.lower :=
  (incident_outer_owner l hl groups.lower_mem hg (groups.lower_side.trans hs.symm) groups.lower_port hk).symm

private theorem group_of_endpoint (l : PortLayout) {e : Endpoint} (he : e ∈ l.endpoints) :
    ∃ g ∈ placements l, g.side = e.side ∧ (e.port = g.left ∨ e.port = g.right) := by
  obtain ⟨g, hg, he⟩ := List.mem_flatMap.mp he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact ⟨g, hg, rfl, Or.inl rfl⟩
  · exact ⟨g, hg, rfl, Or.inr rfl⟩

/-- Every actual port selects its actual upper WIRE and lower incident group. -/
theorem axisGroups_nonempty (l : PortLayout) (hl : l.pages.Valid) {k : ℕ} (hk : k < l.portCount) :
    Nonempty (l.AxisGroups k) := by
  obtain ⟨e, he, hes, hep⟩ := l.endpoints_upper_exists hl hk
  obtain ⟨upper, hu, hus, hup⟩ := group_of_endpoint l he
  have hs : upper.side = .upper := hus.trans hes
  have hw : upper.gate = none := by
    cases hg : upper.gate with
    | none => rfl
    | some kind => exact False.elim (by have h := (placement_gate_shape l hu hg).1; rw [hs] at h; cases h)
  have hp : k = upper.left ∨ k = upper.right := by simpa only [hep] using hup
  rcases l.endpoints_lower_or_gate hl hk with hend | ⟨kind, first, hraw, hfirst⟩
  · obtain ⟨f, hf, hfs, hfp⟩ := hend
    obtain ⟨lower, hlow, hls, hlp⟩ := group_of_endpoint l hf
    exact ⟨⟨upper, hu, hs, hw, hp, lower, hlow, hls.trans hfs, by
      rcases hlp with h | h
      · exact Or.inl (hfp.symm.trans h)
      · exact Or.inr (Or.inl (hfp.symm.trans h))⟩⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hraw
    let lower : Placement := ⟨.lower, first, first + 2, l.lowerLevel i, l.lowerOffset i, some kind⟩
    have hlow : lower ∈ placements l := by
      apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨(.gate kind first, i.val), List.mem_zipIdx_iff_getElem?.mpr ?_, rfl⟩
      rw [List.getElem?_eq_getElem i.isLt]
      exact congrArg some hi
    exact ⟨⟨upper, hu, hs, hw, hp, lower, hlow, rfl, Or.inr (Or.inr ⟨rfl, hfirst⟩)⟩⟩

end PushPuzzle.PushS.PortLayout
