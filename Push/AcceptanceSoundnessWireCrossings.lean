/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessColumnRadius
public import PushS.PortWireCrossings
import all PushS.PortWireCrossings
import all PushS.PortWireIndexing
import all PushS.PortEndpointSeparation

/-! Protected ordinary WIRE crossings on actual accepted trajectories. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- Crossings of an actual ordinary WIRE with a shallower endpoint's column remain occupied
and are never reached by the player in a successful physical play. -/
theorem canonical_wire_crossing (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ []) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {e : Endpoint} (he : e ∈ l.endpoints) (hside : e.side = g.side)
    (hleft : g.left < e.port) (hright : e.port < g.right)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : Nat.dist q.1.val (p.x e.port) ≤ p.L p.levels + 12)
    (hy : q.2.val = if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    u.player ≠ q ∧ q ∈ u.boxes := by
  have hlevel := interior_endpoint_shallower l hl hg hw he hside hleft hright
  have hglevel := placement_level_bounds l hl hg
  have heM : e.level < p.levels := by omega
  have hband := crossing_band l p hl hM hg hw he hside hleft hright hx hy
  obtain ⟨hlo, hhi⟩ := interior_column_bounds p hleft hright hx
  exact ⟨canonical_endpoint_deep_unvisited l p hl hM haxes initial target hgate e he heM hband hsu hut ha,
    canonical_endpoint_deep_occupied l p hl hM haxes initial target hgate e he heM hband
      (l.physicalInstance_wireInterior_initial_full p hl hM haxes (l.canonical initial) (l.canonical target) hg hw hy hlo hhi) hsu hut ha⟩

/-- Crossings of an actual lower WIRE with a three-port middle column stay occupied
and cannot be visited during a successful physical play. -/
theorem canonical_wire_gate_crossing (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ []) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    (hside : g.side = .lower) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    (hleft : g.left < middle) (hright : middle < g.right)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : Nat.dist q.1.val (p.x middle) ≤ p.L p.levels + 12)
    (hy : q.2.val = p.H - readDepth p g.level)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    u.player ≠ q ∧ q ∈ u.boxes := by
  obtain ⟨hlevels, hband⟩ := gate_crossing_band l p hl hM hg hw hside hx hy
  obtain ⟨hlo, hhi⟩ := interior_column_bounds p hleft hright hx
  have hy' : q.2.val = if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level := by
    simpa only [hside, reduceCtorEq, ite_false] using hy
  exact ⟨canonical_gate_deep_unvisited l p hl hM haxes initial target hgate hi hlevels hband hsu hut ha,
    canonical_gate_deep_occupied l p hl hM haxes initial target hgate hi hlevels hband
      (l.physicalInstance_wireInterior_initial_full p hl hM haxes (l.canonical initial) (l.canonical target) hg hw hy' hlo hhi) hsu hut ha⟩

end PushPuzzle.Push.AcceptanceSoundness
