/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGatePageWindow
public import PushS.PortPageBackground
import all PushS.PortPageClosure
import all PushS.PortGatePageWindow
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality
import all PushS.PortStreetSeparation
import all PushS.PortSegments

/-! Actual player columns immediately above and below a three-port working row. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- A successful player one row from a gate's work row must stand on one of its six actual page columns. -/
theorem physicalInstance_gate_player_adjacent_columns {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals)
    (hrow : u.player.2.val + 1 = p.H - readDepth p 1 ∨ u.player.2.val = p.H - readDepth p 1 + 1)
    (hnear : Nat.dist u.player.1.val (p.x (g.left + 1)) ≤ p.L p.levels + 12) :
    u.player.1.val ∈ p.x (g.left + 1) :: gateSpecialColumns p (g.left + 1) := by
  have hs := l.physicalInstance_player_on_pages p hl hM ha initial target hsu hut ht
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have hside : p.D < u.player.2.val := by omega
  rcases (l.page_support_iff_side p hl .lower u.player hside).mp hs with hy | hx
  · have he := l.workingRowSet_even p hy
    have hYe := readDepth_even p 1
    have hHe := H_even p
    omega
  · have hi := center_of_gate l (placement_gate_mem l hg hk)
    exact l.gatePageColumns_near p hl ha hi hx hnear

/-- A successful player one row from the work row cannot stand above or below any relay-fault J cell. -/
theorem physicalInstance_gate_relay_vertical_excluded {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals)
    (hrow : u.player.2.val + 1 = p.H - readDepth p 1 ∨ u.player.2.val = p.H - readDepth p 1 + 1)
    (hx : 9 ≤ (u.player.1.val : ℤ) - p.x (g.left + 1) ∧ (u.player.1.val : ℤ) - p.x (g.left + 1) ≤ 11) : False := by
  have hc := l.physicalInstance_gate_player_adjacent_columns p hl hM ha initial target hg hk hsu hut ht hrow
    (by simp only [Nat.dist]; omega)
  have hcx : (coordinates p).x = p.x := rfl
  simp only [gateSpecialColumns, specialColumns, hcx, List.mem_cons, List.not_mem_nil, or_false] at hc
  omega

end Solution
end PushPuzzle.PushS.PortLayout
