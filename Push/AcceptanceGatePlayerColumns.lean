/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessPages
public import PushS.PortGatePlayerColumns
import all PushS.PortPageClosure
import all PushS.PortGatePageWindow
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality
import all PushS.PortStreetSeparation
import all PushS.PortSegments

/-! Real accepted players near a gate's working row use its original six adjacent page columns. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

/-- An accepted player beside the gate working row stands on one of the actual six page columns. -/
theorem canonical_gate_player_adjacent_columns {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (row : u.player.2.val + 1 = p.H - readDepth p 1 ∨ u.player.2.val = p.H - readDepth p 1 + 1)
    (near : Nat.dist u.player.1.val (p.x (g.left + 1)) ≤ p.L p.levels + 12) :
    u.player.1.val ∈ p.x (g.left + 1) :: gateSpecialColumns p (g.left + 1) := by
  have supported := canonical_player_on_pages l p hl hM haxes initial target hsu hut accepted
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have side : p.D < u.player.2.val := by omega
  rcases (l.page_support_iff_side p hl .lower u.player side).mp supported with hy | hx
  · have even := l.workingRowSet_even p hy
    have hYe := readDepth_even p 1
    have hHe := H_even p
    omega
  · have middle := center_of_gate l (placement_gate_mem l hg hk)
    exact l.gatePageColumns_near p hl haxes middle hx near

/-- A real accepted player cannot stand one row above or below a relay-fault J cell. -/
theorem canonical_gate_relay_vertical_excluded {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (row : u.player.2.val + 1 = p.H - readDepth p 1 ∨ u.player.2.val = p.H - readDepth p 1 + 1)
    (column : 9 ≤ (u.player.1.val : ℤ) - p.x (g.left + 1) ∧
      (u.player.1.val : ℤ) - p.x (g.left + 1) ≤ 11) : False := by
  have cols := canonical_gate_player_adjacent_columns l p hl hM haxes initial target hg hk hsu hut accepted row
    (by simp only [Nat.dist]; omega)
  have hx : (coordinates p).x = p.x := rfl
  simp only [gateSpecialColumns, specialColumns, hx, List.mem_cons, List.not_mem_nil, or_false] at cols
  omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
