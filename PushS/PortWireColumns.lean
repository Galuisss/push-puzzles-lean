/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortWireRail
import all PushS.PortWireIndexing
import all PushS.PortWireGeometry
import all PushS.PortStreetEnumeration
import all PushS.PortCoreCrossing
import all PushS.PortWalkBudget
import all PushS.PortSegments

/-! Every internal page column of an actual ordinary WIRE is a protected deep crossing. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

private theorem wire_pageColumn_owner (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {q : Cell (p.W + 1) (p.H + 1)} (hr : q ∈ wireOpenRail p g)
    (hc : q.1 ∈ l.pageColumnSet p g.side) :
    q.1.val = p.x g.left + 2 ∨ q.1.val = p.x g.right - 2 ∨
      (∃ e ∈ l.endpoints, e.side = g.side ∧ g.left < e.port ∧ e.port < g.right ∧
        Nat.dist q.1.val (p.x e.port) ≤ p.L p.levels + 12) ∨
      (g.side = .lower ∧ ∃ middle ∈ l.gateCenterCoordinates,
        g.left < middle ∧ middle < g.right ∧ Nat.dist q.1.val (p.x middle) ≤ p.L p.levels + 12) := by
  have hr := (Finset.mem_filter.mp hr).2
  have hports := wire_ports l hl hg hw
  have hxW := x_add_readLength_lt_W p (hports.2.trans_le ha) 0
  have hd := p.outer_distance
  change q.1.val ∈ pageColumns l (coordinates p) g.side at hc
  simp only [pageColumns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
  rcases hc with hx | hx | he | hi
  · change q.1.val = 0 at hx
    omega
  · change q.1.val = p.W at hx
    omega
  · obtain ⟨e, he, hcols⟩ := List.mem_flatMap.mp he
    obtain ⟨he, hs⟩ := List.mem_filter.mp he
    have hs : e.side = g.side := of_decide_eq_true hs
    have hspan := endpoint_columns_span p e hcols
    have hb := span_port_bounds p (r := columnRadius p) (by dsimp only [columnRadius]; omega)
      hspan hr.2.1 hr.2.2
    by_cases hleft : e.port = g.left
    · have heq := l.endpoints_key_injective hl he (wire_endpoints l hg hw).1 hs hleft
      subst e
      change q.1.val ∈ [p.x g.left - readLength p g.level, p.x g.left, p.x g.left + 2] at hcols
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcols
      exact Or.inl (by omega)
    · by_cases hright : e.port = g.right
      · have heq := l.endpoints_key_injective hl he (wire_endpoints l hg hw).2 hs hright
        subst e
        change q.1.val ∈ [p.x g.right + readLength p g.level, p.x g.right, p.x g.right - 2] at hcols
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hcols
        exact Or.inr (Or.inl (by omega))
      · refine Or.inr (Or.inr (Or.inl ⟨e, he, hs, by omega, by omega, ?_⟩))
        simp only [Nat.dist]
        dsimp only [columnRadius] at hspan
        omega
  · split at hi
    · rename_i hs
      obtain ⟨middle, hi, hcols⟩ := List.mem_flatMap.mp hi
      have hspan := center_columns_span p middle hcols
      have hb := span_port_bounds p (r := columnRadius p) (by dsimp only [columnRadius]; omega)
        hspan hr.2.1 hr.2.2
      obtain ⟨kind, first, hgate, hm⟩ := center_gate_mem l hi
      have hleft : middle ≠ g.left := by
        intro he
        exact l.endpoints_lower_ne_gate_middle hl hgate (wire_endpoints l hg hw).1 hs (he.symm.trans hm)
      have hright : middle ≠ g.right := by
        intro he
        exact l.endpoints_lower_ne_gate_middle hl hgate (wire_endpoints l hg hw).2 hs (he.symm.trans hm)
      refine Or.inr (Or.inr (Or.inr ⟨hs, middle, hi, by omega, by omega, ?_⟩))
      simp only [Nat.dist]
      dsimp only [columnRadius] at hspan
      omega
    · cases hi

/-- Apart from the two receiving columns, every page-column intersection of an open WIRE
stays occupied and cannot be visited in an actual successful play. -/
theorem physicalInstance_wire_internal_column (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {q : Cell (p.W + 1) (p.H + 1)} (hr : q ∈ wireOpenRail p g)
    (hc : q.1 ∈ l.pageColumnSet p g.side)
    (hleft : q.1.val ≠ p.x g.left + 2) (hright : q.1.val ≠ p.x g.right - 2)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    u.player ≠ q ∧ q ∈ u.boxes := by
  have hy := (Finset.mem_filter.mp hr).2.1
  rcases wire_pageColumn_owner l p hl ha hg hw hr hc with hx | hx | ⟨e, he, hs, hl', hr', hx⟩ |
      ⟨hs, middle, hi, hl', hr', hx⟩
  · exact False.elim (hleft hx)
  · exact False.elim (hright hx)
  · exact l.physicalInstance_wire_crossing p hl hM ha initial target hg hw he hs hl' hr' hx hy hsu hut ht
  · have hy' : q.2.val = p.H - readDepth p g.level := by
      simpa only [hs, reduceCtorEq, ite_false] using hy
    exact l.physicalInstance_wire_gate_crossing p hl hM ha initial target hg hw hs hi hl' hr' hx hy' hsu hut ht

end PushPuzzle.PushS.PortLayout
