/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateRail
import all PushS.PortGateRail
import all PushS.PortGateIndexing
import all PushS.PortStreetEnumeration
import all PushS.PortCoreCrossing
import all PushS.PortWalkBudget
import all PushS.PortWireGeometry
import all PushS.PortSegments

/-! The lower page columns crossing an actual three-port horizontal rail. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- Only the two receiving columns and the gate's own six core columns cross its open rail. -/
theorem gateOpenRail_page_columns (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {q : Cell (p.W + 1) (p.H + 1)} (hr : q ∈ gateOpenRail p g)
    (hc : q.1 ∈ l.pageColumnSet p .lower) :
    q.1.val = p.x g.left + 2 ∨ q.1.val = p.x g.right - 2 ∨ q.1.val = p.x (g.left + 1) ∨
      q.1.val ∈ gateSpecialColumns p (g.left + 1) := by
  have hr := (Finset.mem_filter.mp hr).2
  have hports := gate_port_bounds l hl hg hk
  have hxW := x_add_readLength_lt_W p (hports.2.trans_le ha) 0
  have hd := p.outer_distance
  have hshape := placement_gate_shape l hg hk
  change q.1.val ∈ pageColumns l (coordinates p) .lower at hc
  simp only [pageColumns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc, ite_true] at hc
  rcases hc with hx | hx | he | hi
  · change q.1.val = 0 at hx
    omega
  · change q.1.val = p.W at hx
    omega
  · obtain ⟨e, he, hcols⟩ := List.mem_flatMap.mp he
    obtain ⟨he, hs⟩ := List.mem_filter.mp he
    have hs : e.side = .lower := of_decide_eq_true hs
    have hspan := endpoint_columns_span p e hcols
    rcases gate_endpoint_between l p hl hg hk he hs (r := columnRadius p)
        (by dsimp only [columnRadius]; omega) hspan hr.2.1 hr.2.2 with rfl | rfl
    · change q.1.val ∈ [p.x g.left - readLength p g.level, p.x g.left, p.x g.left + 2] at hcols
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcols
      exact Or.inl (by omega)
    · change q.1.val ∈ [p.x g.right + readLength p g.level, p.x g.right, p.x g.right - 2] at hcols
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcols
      exact Or.inr (Or.inl (by omega))
  · obtain ⟨middle, hi, hcols⟩ := List.mem_flatMap.mp hi
    have hspan := center_columns_span p middle hcols
    have hb := span_port_bounds p (r := columnRadius p) (by dsimp only [columnRadius]; omega)
      hspan hr.2.1 hr.2.2
    obtain ⟨other, first, hgate, hm⟩ := center_gate_mem l hi
    have hleft : middle ≠ g.left := by
      intro he
      exact l.endpoints_lower_ne_gate_middle hl hgate (gate_endpoints l hg hk).1 hshape.1 (he.symm.trans hm)
    have hright : middle ≠ g.right := by
      intro he
      exact l.endpoints_lower_ne_gate_middle hl hgate (gate_endpoints l hg hk).2 hshape.1 (he.symm.trans hm)
    have heq : middle = g.left + 1 := by omega
    change q.1.val ∈ p.x middle :: gateSpecialColumns p middle at hcols
    rw [heq] at hcols
    exact Or.inr (Or.inr (List.mem_cons.mp hcols))

end PushPuzzle.PushS.PortLayout
