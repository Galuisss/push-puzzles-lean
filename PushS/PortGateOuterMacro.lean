/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateUpdates
public import PushS.LinePush
import all PushS.PortGateUpdates
import all PushS.PortGateRail
import all PushS.PortGateIndexing
import all PushS.PortWireIndexing
import all PushS.PortCoreCrossing
import all PushS.PortSegments

/-! Genuine long-train pushes for the two outer internal signals of an actual three-port group. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private def outerPlayerX (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind)
    (right gain : Bool) : ℕ :=
  if gain then outerFirstX p g kind right gain - 1 else outerFirstX p g kind right gain + 1

private def outerLength (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind) (right : Bool) : ℕ :=
  if right then p.x g.right - p.x (g.left + 1) - 14
  else p.x (g.left + 1) - p.x g.left - kind.kappa.toNat

private theorem outerFirstX_bounded (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) (right gain : Bool) :
    outerFirstX p g kind right gain < p.W + 1 := by
  have hs := placement_gate_shape l hg hk
  have hright := axis_spacing p (show g.left + 1 < g.right by omega)
  have hleft := axis_spacing p (show g.left < g.left + 1 by omega)
  have hW := x_add_readLength_lt_W p ((gate_port_bounds l hl hg hk).2.trans_le ha) 0
  have hD := p.outer_distance
  cases right <;> cases gain <;> simp only [outerFirstX, Bool.false_eq_true, ite_false, ite_true] <;> omega

private theorem gate_outer_step (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) (right gain : Bool)
    (hi : outerSlot g right < state.internal.length)
    (hbefore : state.internal.getD (outerSlot g right) false = !gain)
    (s : HoleState (p.W + 1) (p.H + 1))
    (hempty : s.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hp : (s.player.1.val, s.player.2.val) = (outerPlayerX p g kind right gain, p.H - readDepth p 1))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    ∃ t : HoleState (p.W + 1) (p.H + 1), Step B none s.toState t.toState ∧
      t.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (l.encodedSegments p {state with internal := state.internal.set (outerSlot g right) gain}) ∧
      (t.player.1.val, t.player.2.val) = (outerFirstX p g kind right gain, p.H - readDepth p 1) := by
  let q : Cell (p.W + 1) (p.H + 1) :=
    (⟨outerFirstX p g kind right gain, outerFirstX_bounded l p hl ha hg hk right gain⟩, s.player.2)
  let z : Cell (p.W + 1) (p.H + 1) :=
    (⟨outerFirstX p g kind right (!gain), outerFirstX_bounded l p hl ha hg hk right (!gain)⟩, s.player.2)
  have hpy : s.player.2.val = p.H - readDepth p 1 := congrArg Prod.snd hp
  have hpx : s.player.1.val = outerPlayerX p g kind right gain := congrArg Prod.fst hp
  have htarget := gate_outer_update l p hl hM ha state hg hk right gain hi hbefore q z rfl rfl hpy hpy
  let t : HoleState (p.W + 1) (p.H + 1) := {
    player := q
    empty := SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (l.encodedSegments p {state with internal := state.internal.set (outerSlot g right) gain})
    player_empty := by rw [htarget]; exact Finset.mem_insert_self _ _ }
  obtain ⟨hs, hleft, hright, hD, hkappa, hshort, hleftBit, hrightBit, hrightNot, hx0, hxR⟩ :=
    gate_outer_geometry l p state hg hk
  have hzR := outer_transfer_in_rail l p hg hk (q := z) hpy (by
    cases right <;> cases gain <;> simp [z, outerFirstX])
  have hmove : Move B none (if gain then .east else .west) s.toState t.toState := by
    apply HoleState.move_to_first_hole s t (if gain then .east else .west) z (outerLength p g kind right)
      (by cases right <;> simp only [outerLength, Bool.false_eq_true, ite_false, ite_true] <;> omega) ?_ ?_ ?_ ?_ ?_ ?_ B hB
    · cases gain <;> rfl
    · cases right <;> cases gain <;>
        simp only [Direction.position, outerPlayerX, outerFirstX, outerLength, Bool.false_eq_true,
          ite_false, ite_true, Bool.not_false, Bool.not_true, z] at hpx ⊢ <;> omega
    · intro r hLane hlo hhi hrH
      have hry : r.2.val = p.H - readDepth p 1 := by
        cases gain <;> exact hLane.trans hpy
      have hrRail : r ∈ gateOpenRail p g := by
        have hz := (Finset.mem_filter.mp hzR).2
        cases right <;> cases gain <;>
          simp only [Direction.position, outerPlayerX, outerFirstX, Bool.false_eq_true, ite_false,
            ite_true, Bool.not_false, Bool.not_true, z] at hlo hhi hpx <;>
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hry, by omega, by omega⟩
      rw [hempty, l.encodedSegments_gateOpenRail_mem p hl hM ha state hg hk hrRail] at hrH
      cases right <;> cases gain <;>
        simp only [outerSlot, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero, Bool.not_false,
          Bool.not_true] at hbefore <;>
        simp only [Direction.position, outerPlayerX, outerFirstX, Bool.false_eq_true, ite_false,
          ite_true, Bool.not_false, Bool.not_true, z] at hlo hhi hpx <;>
        simp only [hbefore, Bool.not_false, Bool.not_true, Bool.toNat_false, Bool.toNat_true] at hrH <;> omega
    · rw [hempty, l.encodedSegments_gateOpenRail_mem p hl hM ha state hg hk hzR]
      cases right <;> cases gain <;>
        simp only [outerSlot, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero, Bool.not_false,
          Bool.not_true] at hbefore <;>
        simp only [hbefore, outerFirstX, Bool.false_eq_true, ite_false, ite_true, Bool.not_false,
          Bool.not_true, Bool.toNat_false, Bool.toNat_true, z] <;> omega
    · cases right <;> cases gain <;>
        simp only [Adjacent, outerPlayerX, outerFirstX, Bool.false_eq_true, ite_false,
          ite_true, t, q] at hpx ⊢ <;> constructor <;> first | omega | trivial
    · change _ = insert q (s.empty.erase z)
      rw [hempty]
      exact htarget
  exact ⟨t, ⟨_, hmove⟩, rfl, by change (_, s.player.2.val) = _; rw [hpy]⟩

/-- One complete left long-train push flips the actual left internal signal on the marked board. -/
theorem encodedSegments_gate_left_step (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) (hi : g.internal < state.internal.length)
    (gain : Bool) (hbefore : state.internal.getD g.internal false = !gain)
    (s : HoleState (p.W + 1) (p.H + 1))
    (hempty : s.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hp : (s.player.1.val, s.player.2.val) =
      (if gain then p.x g.left + 1 else p.x (g.left + 1) + 3 - kind.kappa.toNat, p.H - readDepth p 1))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    ∃ t : HoleState (p.W + 1) (p.H + 1), Step B none s.toState t.toState ∧
      t.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (l.encodedSegments p {state with internal := state.internal.set g.internal gain}) ∧
      (t.player.1.val, t.player.2.val) =
        (if gain then p.x g.left + 2 else p.x (g.left + 1) + 2 - kind.kappa.toNat, p.H - readDepth p 1) := by
  apply gate_outer_step l p hl hM ha state hg hk false gain hi hbefore s hempty ?_ B hB
  apply Prod.ext
  · have hpx := congrArg Prod.fst hp
    have hx0 := readLength_add_lt_x p (g.left + 1) 0
    have hkappa : kind.kappa.toNat ≤ 4 := by cases kind <;> decide +kernel
    cases gain <;> simp only [outerPlayerX, outerFirstX, Bool.false_eq_true, ite_false, ite_true] at hpx ⊢ <;> omega
  · have hpy := congrArg Prod.snd hp
    exact hpy

/-- One complete right long-train push flips the actual relay signal on the marked board. -/
theorem encodedSegments_gate_right_step (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) (hi : g.internal + 2 < state.internal.length)
    (gain : Bool) (hbefore : state.internal.getD (g.internal + 2) false = !gain)
    (s : HoleState (p.W + 1) (p.H + 1))
    (hempty : s.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hp : (s.player.1.val, s.player.2.val) =
      (if gain then p.x (g.left + 1) + 11 else p.x g.right - 1, p.H - readDepth p 1))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    ∃ t : HoleState (p.W + 1) (p.H + 1), Step B none s.toState t.toState ∧
      t.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (l.encodedSegments p {state with internal := state.internal.set (g.internal + 2) gain}) ∧
      (t.player.1.val, t.player.2.val) =
        (if gain then p.x (g.left + 1) + 12 else p.x g.right - 2, p.H - readDepth p 1) := by
  apply gate_outer_step l p hl hM ha state hg hk true gain hi hbefore s hempty ?_ B hB
  apply Prod.ext
  · have hpx := congrArg Prod.fst hp
    have hxR := readLength_add_lt_x p g.right 0
    cases gain <;> simp only [outerPlayerX, outerFirstX, Bool.false_eq_true, ite_false, ite_true] at hpx ⊢ <;> omega
  · have hpy := congrArg Prod.snd hp
    exact hpy

end PushPuzzle.PushS.PortLayout
