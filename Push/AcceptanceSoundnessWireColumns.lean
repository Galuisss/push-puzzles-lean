/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWireCrossings
public import PushS.PortWireColumns
import all PushS.PortWireColumns
import all PushS.PortWireIndexing
import all PushS.PortEndpointSeparation

/-! Protected internal WIRE columns on actual accepted trajectories. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- Apart from the two receiving columns, every page-column intersection of an open WIRE
stays occupied and cannot be visited in an actual successful play. -/
theorem canonical_wire_internal_column (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ []) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {q : Cell (p.W + 1) (p.H + 1)} (hr : q ∈ wireOpenRail p g)
    (hc : q.1 ∈ l.pageColumnSet p g.side)
    (hleft : q.1.val ≠ p.x g.left + 2) (hright : q.1.val ≠ p.x g.right - 2)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    u.player ≠ q ∧ q ∈ u.boxes := by
  have hy := (Finset.mem_filter.mp hr).2.1
  rcases wire_pageColumn_owner l p hl haxes hg hw hr hc with hx | hx | ⟨e, he, hs, hl', hr', hx⟩ |
      ⟨hs, middle, hi, hl', hr', hx⟩
  · exact False.elim (hleft hx)
  · exact False.elim (hright hx)
  · exact canonical_wire_crossing l p hl hM haxes initial target hgate hg hw he hs hl' hr' hx hy hsu hut ha
  · have hy' : q.2.val = p.H - readDepth p g.level := by
      simpa only [hs, reduceCtorEq, ite_false] using hy
    exact canonical_wire_gate_crossing l p hl hM haxes initial target hgate hg hw hs hi hl' hr' hx hy' hsu hut ha

end PushPuzzle.Push.AcceptanceSoundness
