/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortOrdinaryBlockers
import all PushS.PortOrdinaryBlockers
import all PushS.PortEndpointReaderFreeze
import all PushS.PortEndpointLevelReader
import all PushS.PortEndpointRWall
import all PushS.PortEndpointLevelRWall
import all PushS.PortSegments

/-! The inward axis neighbour on the ordinary branch row belongs to the actual reader closure. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- The actual reader closure blocks the axis's inward neighbour on its depth-plus-two row. -/
theorem endpointOrdinaryBlockers_branch_mem (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = if e.inward then p.x e.port + 1 else p.x e.port - 1)
    (hy : q.2.val = if e.side = .upper then readDepth p e.level + 2
      else p.H - (readDepth p e.level + 2)) :
    q ∈ l.endpointOrdinaryBlockers p hl hM ha e he := by
  by_cases hlast : e.level = p.levels
  · let g := lastReaderSeparator l p hl ha e he
    have hrow : InwardRow p e g.cell q := by
      refine ⟨Fin.ext ?_, ?_⟩
      · rw [g.row]
        simpa only [hlast, readDepth_eq p p.levels_pos le_rfl] using hy
      · have hg := g.forward
        have hx0 := readLength_add_lt_x p e.port 0
        cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false] at hx hg ⊢ <;> omega
    rcases r_wall_row_point l p hl e g q hrow with hwall | hpage
    · simp only [endpointOrdinaryBlockers, hlast, ite_true, endpointReaderBlockers]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hwall)
    · simp only [endpointOrdinaryBlockers, hlast, ite_true]
      exact reader_page_subset l p hl hM ha e he hpage
  · let g := levelReaderSeparator l p hl hM ha e he
    have hm := l.levelRWall_branch_back_mem p hl e g hx hy
    rcases Finset.mem_union.mp hm with hpage | hwall
    · simp only [endpointOrdinaryBlockers, hlast, ite_false]
      exact level_reader_page l p hl hM ha e he hpage
    · simp only [endpointOrdinaryBlockers, hlast, ite_false, endpointLevelReaderBlockers]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hwall))

end PushPuzzle.PushS.PortLayout
