/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateFrameMacro
public import PushS.PortWireMacro
public import PushS.PortAxisMacro
import all PushS.PortGateFrameMacro
import all PushS.PortEndpointPocket
import all PushS.PortEndpointConnections
import all PushS.PortWireMacro
import all PushS.PortWireIndexing
import all PushS.PortSegments

/-! Actual ordinary horizontal and shared-axis flips with concrete frame access and return. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- A supplied ordinary WIRE actuator flips its signal on the full board and returns to the frame. -/
theorem encodedSegments_wire_from_frame (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    (hi : g.internal < state.internal.length) (gain : Bool) (hbefore : state.internal.getD g.internal false = !gain)
    (hstand : (if g.side = .upper then state.axes.getD (if gain then g.left else g.right) false
      else !(state.axes.getD (if gain then g.left else g.right) false)) = true)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Reachable B none (l.cornerState p state).toState
      (l.cornerState p {state with internal := state.internal.set g.internal gain}).toState := by
  let e := if gain then wireLeft g else wireRight g
  have he : e ∈ l.endpoints := by
    have hp := wire_endpoints l hg hw
    cases gain
    · exact hp.2
    · exact hp.1
  have haxis : axisInput state e = true := by
    cases gain <;> simpa only [e, wireLeft, wireRight, axisInput, Bool.false_eq_true, ite_false, ite_true] using hstand
  let q := pocketCell l p hl ha e he 1 (readDepth p e.level) (by omega)
  have hq := horizontal_slot_mem p state e (q := q) 1 le_rfl (by omega) rfl rfl
  have hstart := l.endpointPocket_connected p hl hM ha state e he (Or.inl haxis) q
    ((finite_take_drop p _ 1 q).mpr (Or.inr hq)) B hB none
  let s := (l.cornerState p state).walk q (hstart.point_hole hB)
  have hrow : onSide (coordinates p) e.side (readDepth p e.level) =
      (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level) := by cases gain <;> rfl
  have hfirst : inward (p.x e.port) e.inward 1 = (if gain then p.x g.left + 1 else p.x g.right - 1) := by
    cases gain <;> rfl
  obtain ⟨t, hm, ht, hp⟩ := full_wire_step l p hl hM ha state hg hw hi gain hbefore s rfl (Prod.ext hfirst hrow) B hB
  have htx := congrArg Prod.fst hp
  have hty := congrArg Prod.snd hp
  have hnext : inward (p.x e.port) e.inward 2 = (if gain then p.x g.left + 2 else p.x g.right - 2) := by
    cases gain <;> rfl
  have hself : (state.internal.set g.internal gain).getD g.internal false = gain := List.getD_set_self hi
  have hrecv : horizontalInput {state with internal := state.internal.set g.internal gain} e = true := by
    cases gain <;> simp only [e, wireLeft, wireRight, horizontalInput, Bool.false_eq_true, ite_false, ite_true, hself, Bool.not_false]
  have hfinish := horizontal_station_connected l p hl hM ha _ e he hrecv t.player 2 (by omega) le_rfl
    (htx.trans hnext.symm) (hty.trans hrow.symm) B hB
  exact complete_step_from_frame l p state _ B s t rfl ht hstart hm hfinish

/-- A supplied ordinary shared-axis actuator flips its signal on the full board and returns to the frame. -/
theorem encodedSegments_axis_from_frame (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) (upper lower : Endpoint) (hu : upper ∈ l.endpoints) (hlower : lower ∈ l.endpoints)
    (hsu : upper.side = .upper) (hsl : lower.side = .lower) (hport : lower.port = upper.port)
    (hi : upper.port < state.axes.length) (gain : Bool) (hbefore : state.axes.getD upper.port false = !gain)
    (hstand : (if gain then
        (if upper.inward then state.internal.getD upper.internal false else !(state.internal.getD upper.internal false))
      else (if lower.inward then state.internal.getD lower.internal false else !(state.internal.getD lower.internal false))) = true)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Reachable B none (l.cornerState p state).toState
      (l.cornerState p {state with axes := state.axes.set upper.port gain}).toState := by
  let e := if gain then upper else lower
  have he : e ∈ l.endpoints := by cases gain <;> assumption
  have hrecv : horizontalInput state e = true := by
    cases gain <;> simpa only [e, horizontalInput, Bool.false_eq_true, ite_false, ite_true] using hstand
  let q := pocketCell l p hl ha e he 0 (readDepth p e.level + 1) (by omega)
  have hqx := pocket_axis_column l p hl ha e he (readDepth p e.level + 1) (by omega)
  have hq := axis_slot_mem p state e (q := q) hqx _ (by omega) (by omega) rfl
  have hstart := l.endpointPocket_connected p hl hM ha state e he (Or.inr hrecv) q
    ((finite_take_drop p _ 1 q).mpr (Or.inl hq)) B hB none
  let s := (l.cornerState p state).walk q (hstart.point_hole hB)
  have hep : e.port = upper.port := by cases gain <;> first | exact hport | rfl
  have hrow (d : ℕ) : onSide (coordinates p) e.side (readDepth p e.level + d) =
      (if gain then readDepth p upper.level + d else p.H - readDepth p lower.level - d) := by
    cases gain
    · simp only [e, Bool.false_eq_true, ite_false, hsl, onSide, reduceCtorEq, show (coordinates p).H = p.H from rfl]
      omega
    · simp only [e, ite_true, hsu, onSide]
  obtain ⟨t, hm, ht, hp⟩ := l.encodedSegments_axis_step p hl hM ha state upper lower hu hlower hsu hsl hport hi gain hbefore s rfl
    (Prod.ext (by have hx : s.player.1.val = p.x e.port := hqx; simpa only [hep] using hx) (hrow 1)) B hB
  have htx := congrArg Prod.fst hp
  have hty := congrArg Prod.snd hp
  have hself : (state.axes.set upper.port gain).getD upper.port false = gain := List.getD_set_self hi
  have haxis : axisInput {state with axes := state.axes.set upper.port gain} e = true := by
    cases gain <;> simp only [e, axisInput, Bool.false_eq_true, ite_false, ite_true, hsu, hsl,
      reduceCtorEq, hport, hself, Bool.not_false]
  have hfinish := axis_station_connected l p hl hM ha _ e he haxis t.player (readDepth p e.level + 2)
    (by omega) le_rfl (by simpa only [hep] using htx) (hty.trans (hrow 2).symm) B hB
  exact complete_step_from_frame l p state _ B s t rfl ht hstart hm hfinish

end PushPuzzle.PushS.PortLayout
