/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import Push.AcceptanceGatePrivateClosure
public import PushS.PortGatePrivateEntry
import all PushS.PortGatePrivateEntry
import all PushS.PortGatePrivateWalk

/-! Actual accepted trajectories enter the private gate branch through its two geometric entrances. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- A real successful player step entering the five private cells comes from work-row four or the adjacent axis hole. -/
theorem canonical_gate_private_entry_of_walks {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (AcceptanceProgram.instructions (AcceptanceProgram.program l p target).rounds) (holes t))
    (deeper : DeeperWalkInvariant l p hl hM haxes initial target 1 t)
    (walks : PublicWalkInvariant l p hl hM haxes initial target t)
    (hout : u.player ∉ gatePrivateCells p middle) (hin : v.player ∈ gatePrivateCells p middle) :
    (u.player.1.val = p.x middle + 4 ∧ u.player.2.val = p.H - readDepth p 1) ∨
      (u.player.1.val = p.x middle ∧ u.player.2.val = p.H - (readDepth p 1 + 2)) := by
  have hadj := players_adjacent hm.choose_spec
  have hpaths := canonical_gate_private_avoiding_of_walks l p hl hM haxes initial target hgate hi hsu
    ((Relation.ReflTransGen.single hm).trans hvt) accepted deeper walks
  have blocked (hmem : u.player ∈ l.gatePrivateBlockers p hl hM haxes hi)
      (hx : p.x middle < u.player.1.val ∧ u.player.1.val ≤ p.x middle + 5)
      (hy : p.H - (readDepth p 1 + 3) ≤ u.player.2.val ∧ u.player.2.val ≤ p.H - (readDepth p 1 + 1)) : False :=
    hm.choose_spec.valid_source.2.2 (avoiding_box hpaths hmem
      (boundary_initial_box l p hl hM haxes (l.canonical initial) (l.canonical target) hi hx hy hout))
  rcases outside_neighbor p middle hadj hout hin with hentry | ⟨hx, hfour, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact hentry
  · have hguard : u.player ∈ l.gatePrivateBlockers p hl hM haxes hi := by
      rcases hy with hy | hy
      · exact private_near_background l p hl hM haxes hi hx hfour (Or.inl rfl) hy
      · exact private_near_background l p hl hM haxes hi hx hfour (Or.inr rfl) hy
    exact False.elim (blocked hguard ⟨hx.1, by omega⟩ (by rcases hy with h | h <;> omega))
  · exact False.elim (blocked (private_deep l p hl hM haxes hi hx hy) (by omega) (by omega))
  · exact False.elim (blocked (private_bottom l p hl hM haxes hi (Or.inr hx) hy) (by omega) (by omega))

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
