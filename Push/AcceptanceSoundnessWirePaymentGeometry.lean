/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWireTrimStock
public import Push.AcceptanceProgramHalfStockGeometry
import all Push.AcceptanceSoundnessCentralSamples
import all PushS.PortWireGeometry
import all PushS.PortWireIndexing
import all PushS.PortGateIndexing
import all PushS.PortCoreCrossing
import all PushS.PortSegments

/-! An accepted ordinary WIRE has no hole on main-axis columns or lower gate private/sample columns. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- The only actual rail holes on its own page columns are its two original receiving columns. -/
theorem canonical_wire_receiving_of_page_column {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ PushS.holes t) (hrail : q ∈ wireOpenRail p g)
    (hc : q.1 ∈ l.pageColumnSet p g.side) :
    q.1.val = p.x g.left + 2 ∨ q.1.val = p.x g.right - 2 := by
  by_contra hn
  exact (PushS.mem_holes _).mp hq
    (canonical_wire_internal_column l p hl hM haxes initial target hgate hg hw hrail hc
      (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h)) hr .refl ha).2

/-- None of the shared main axes can supply a hole on an actual accepted ordinary rail. -/
theorem canonical_wire_hole_not_axis {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ PushS.holes t) (hrail : q ∈ wireOpenRail p g) :
    q.1.val ∉ axes l p := by
  intro hx
  obtain ⟨i, hi, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  have hc : q.1 ∈ l.mainColumnSet p :=
    (l.mainColumnSet_iff p q.1).mpr (Or.inr (Or.inr ⟨i, List.mem_range.mp hi, he.symm⟩))
  have hrec := canonical_wire_receiving_of_page_column l p hl hM haxes initial target hgate hg hw hr ha hq hrail
    (l.mainColumnSet_subset_pageColumnSet p hl g.side hc)
  have hxR := readLength_add_lt_x p g.right 0
  rcases hrec with h | h
  · exact sample_off_axis p g.left i (offset := 2) (by omega) (h.symm.trans he.symm)
  · exact sample_off_axis p i g.right (offset := 2) (by omega) (by omega)

/-- A lower ordinary rail has no terminal hole anywhere near an interior three-port middle axis. -/
private theorem canonical_wire_lower_gate_near_full {g : Placement} (hg : g ∈ placements l)
    (hw : g.gate = none)
    (hs : g.side = .lower) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hrail : q ∈ wireOpenRail p g)
    (hnear : p.x middle - 12 ≤ q.1.val ∧ q.1.val ≤ p.x middle + 12) : q ∈ t.boxes := by
  have hrow := (Finset.mem_filter.mp hrail).2
  have hD := p.outer_distance
  have hb := span_port_bounds p (r := 12) (by omega) hnear hrow.2.1 hrow.2.2
  obtain ⟨kind, first, hgcenter, hm⟩ := center_gate_mem l hi
  have hleft : middle ≠ g.left := by
    intro he
    exact l.endpoints_lower_ne_gate_middle hl hgcenter (wire_endpoints l hg hw).1 hs (he.symm.trans hm)
  have hright : middle ≠ g.right := by
    intro he
    exact l.endpoints_lower_ne_gate_middle hl hgcenter (wire_endpoints l hg hw).2 hs (he.symm.trans hm)
  have hx : Nat.dist q.1.val (p.x middle) ≤ p.L p.levels + 12 := by
    simp only [Nat.dist]
    omega
  have hy : q.2.val = p.H - readDepth p g.level := by simpa only [hs, reduceCtorEq, ite_false] using hrow.1
  exact (canonical_wire_gate_crossing l p hl hM haxes initial target hgate hg hw hs hi
    (by omega) (by omega) hx hy hr .refl ha).2

/-- Actual lower ordinary rail holes avoid all selected private columns. -/
theorem canonical_wire_lower_hole_not_private {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    (hs : g.side = .lower) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ PushS.holes t) (hrail : q ∈ wireOpenRail p g) :
    q.1.val ∉ privateColumns l p := by
  intro hx
  obtain ⟨middle, hi, hx⟩ := privateColumn_gate l p hx
  exact (PushS.mem_holes _).mp hq
    (canonical_wire_lower_gate_near_full l p hl hM haxes initial target hgate hg hw hs hi hr ha hrail (by omega))

/-- Actual lower ordinary rail holes avoid both selected short-train sample columns. -/
theorem canonical_wire_lower_hole_not_sample {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    (hs : g.side = .lower) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ PushS.holes t) (hrail : q ∈ wireOpenRail p g) :
    q.1.val ∉ samples l p := by
  intro hx
  obtain ⟨middle, hi, hx⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hx)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  apply (PushS.mem_holes _).mp hq
  apply canonical_wire_lower_gate_near_full l p hl hM haxes initial target hgate hg hw hs hi hr ha hrail
  rcases hx with hx | hx <;> omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
