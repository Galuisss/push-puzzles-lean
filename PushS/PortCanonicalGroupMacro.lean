/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortCanonicalUpdate
public import PushS.PortOrdinaryFrameMacro
import all PushS.PortCanonicalUpdate
import all PushS.PortWireIndexing
import all PushS.PortGateIndexing
import all PushS.PortCoreCrossing
import all PushS.PortSegments

/-! Aligning actual incident groups before or after their shared interface-axis flip. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction

/-- Ordinary canonical alignment uses the old axes on the losing page and new axes on the gaining page. -/
theorem encodedSegments_wire_canonicalUpdate_from_frame (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (axes : List Bool) (hlegal : l.InputLegal axes) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {port : ℕ} (gain : Bool) (hbefore : axes.getD port false = !gain)
    (hphase : state.axes = if g.side = .upper then (if gain then axes.set port gain else axes)
      else (if gain then axes else axes.set port gain))
    (hi : g.internal < state.internal.length)
    (hread : state.internal.getD g.internal false = (l.canonical axes).internal.getD g.internal false)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Reachable B none (l.cornerState p state).toState
      (l.cornerState p {state with internal := g.canonicalUpdate state.internal port gain}).toState := by
  by_cases hleft : g.left = port
  · subst port
    have hports := wire_ports l hl hg hw
    have hne : g.left ≠ g.right := by omega
    have hinputs := hlegal.wire_inputs hg hw
    have hslot := hread.trans (l.canonical_wire_read axes hg hw)
    cases hs : g.side with
    | upper =>
      simp only [hs, ite_true] at hphase hinputs hslot
      cases gain
      · simp only [Bool.false_eq_true, ite_false, Bool.not_false] at hphase hbefore
        have hm := l.encodedSegments_wire_from_frame p hl hM ha state hg hw hi true
          (by simpa only [hbefore, Bool.not_true, Bool.not_false] using hslot)
          (by simp only [ite_true, hs, hphase, hbefore]) B hB
        simpa only [Placement.canonicalUpdate, ite_true, hs, Bool.not_false] using hm
      · simp only [ite_true, Bool.not_true] at hphase hbefore
        have hr : axes.getD g.right false = true := hinputs.resolve_left (by intro h; rw [hbefore] at h; cases h)
        have hm := l.encodedSegments_wire_from_frame p hl hM ha state hg hw hi false
          (by simpa only [hbefore, Bool.not_false, Bool.not_true] using hslot)
          (by simp only [Bool.false_eq_true, ite_false, hs, ite_true, hphase, List.getD_set_ne hne, hr]) B hB
        simpa only [Placement.canonicalUpdate, ite_true, hs, Bool.not_true] using hm
    | lower =>
      simp only [hs, reduceCtorEq, ite_false] at hphase hinputs hslot
      cases gain
      · simp only [Bool.false_eq_true, ite_false, Bool.not_false] at hphase hbefore
        have hr : axes.getD g.right false = false := hinputs.resolve_left (by intro h; rw [hbefore] at h; cases h)
        have hm := l.encodedSegments_wire_from_frame p hl hM ha state hg hw hi false
          (by simpa only [hbefore, Bool.not_false] using hslot)
          (by simp only [Bool.false_eq_true, ite_false, hs, reduceCtorEq, hphase, List.getD_set_ne hne, hr, Bool.not_false]) B hB
        simpa only [Placement.canonicalUpdate, ite_true, hs, reduceCtorEq, ite_false] using hm
      · simp only [ite_true, Bool.not_true] at hphase hbefore
        have hm := l.encodedSegments_wire_from_frame p hl hM ha state hg hw hi true
          (by simpa only [hbefore, Bool.not_true] using hslot)
          (by simp only [ite_true, hs, reduceCtorEq, ite_false, hphase, hbefore, Bool.not_false]) B hB
        simpa only [Placement.canonicalUpdate, ite_true, hs, reduceCtorEq, ite_false] using hm
  · have hs : g.canonicalUpdate state.internal port gain = state.internal := by
      simp only [Placement.canonicalUpdate, hleft, ite_false, hw, Option.isSome_none, Bool.false_eq_true, false_and]
    rw [hs]

/-- Gate alignment performs its actual left move or the ordered pair of relay/core moves. -/
theorem encodedSegments_gate_canonicalUpdate_from_frame (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (axes : List Bool) (hlegal : l.InputLegal axes) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {port : ℕ} (gain : Bool) (hbefore : axes.getD port false = !gain)
    (hphase : state.axes = if gain then axes else axes.set port gain)
    (hi : g.internal + 2 < state.internal.length)
    (hread : state.internal.getD g.internal false = axes.getD g.left false ∧
      state.internal.getD (g.internal + 1) false = !(axes.getD g.right false) ∧
      state.internal.getD (g.internal + 2) false = !(axes.getD g.right false))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Reachable B none (l.cornerState p state).toState
      (l.cornerState p {state with internal := g.canonicalUpdate state.internal port gain}).toState := by
  have hs := (placement_gate_shape l hg hk).1
  have hports := gate_port_bounds l hl hg hk
  have hright : g.right = g.left + 2 := (placement_gate_shape l hg hk).2
  have hmid : g.left + 1 < p.axes := by omega
  have hinputs := hlegal.gate_inputs hg hk
  by_cases hleft : g.left = port
  · subst port
    have hslot : state.internal.getD g.internal false = !gain := hread.1.trans hbefore
    have hstand : if gain then state.axes.getD g.left false = false else
        state.internal.getD (g.internal + 1) false = true ∨
          (kind = .orGate ∧ state.axes.getD (g.left + 1) false = false) := by
      cases gain
      · simp only [Bool.false_eq_true, ite_false, Bool.not_false] at hphase hbefore ⊢
        have hne : g.left ≠ g.left + 1 := by omega
        rw [hphase, List.getD_set_ne hne]
        cases kind with
        | andGate =>
          simp only [ite_true] at hinputs
          rcases hinputs with h | ⟨h, _⟩
          · exact Or.inl (by rw [hread.2.1, h]; rfl)
          · rw [hbefore] at h
            cases h
        | orGate =>
          simp only [reduceCtorEq, ite_false] at hinputs
          rcases hinputs with h | h | h
          · rw [hbefore] at h
            cases h
          · exact Or.inr ⟨rfl, h⟩
          · exact Or.inl (by rw [hread.2.1, h]; rfl)
      · simp only [ite_true, Bool.not_true] at hphase hbefore ⊢
        rw [hphase, hbefore]
    have hm := l.encodedSegments_gate_left_from_frame p hl hM ha state hg hk (by omega) gain hslot hstand B hB
    simpa only [Placement.canonicalUpdate, ite_true, hs, reduceCtorEq, ite_false] using hm
  · by_cases hheavy : g.right = port
    · subst port
      have hH : state.internal.getD (g.internal + 1) false = gain := by
        rw [hread.2.1, hbefore, Bool.not_not]
      have hR : state.internal.getD (g.internal + 2) false = gain := by
        rw [hread.2.2, hbefore, Bool.not_not]
      cases gain
      · simp only [Bool.false_eq_true, ite_false] at hphase
        let relay := {state with internal := state.internal.set (g.internal + 2) true}
        have hr := l.encodedSegments_gate_right_from_frame p hl hM ha state hg hk hi true
          (by simpa only [Bool.not_true] using hR) hH B hB
        have hh : relay.internal.getD (g.internal + 1) false = false := by
          change (state.internal.set (g.internal + 2) true).getD (g.internal + 1) false = false
          rw [List.getD_set_ne (by omega), hH]
        have haccess : (kind = .orGate ∧ relay.internal.getD g.internal false = false) ∨
            (relay.axes.getD (g.left + 1) false = false ∧
              (kind = .orGate ∨ relay.internal.getD g.internal false = false)) := by
          have hL : relay.internal.getD g.internal false = axes.getD g.left false := by
            change (state.internal.set (g.internal + 2) true).getD g.internal false = _
            rw [List.getD_set_ne (by omega), hread.1]
          have hC : relay.axes.getD (g.left + 1) false = axes.getD (g.left + 1) false := by
            change state.axes.getD (g.left + 1) false = _
            rw [hphase, List.getD_set_ne (by omega)]
          simp only [Bool.not_false] at hbefore
          cases kind with
          | andGate =>
            simp only [ite_true] at hinputs
            rcases hinputs with h | ⟨hlow, hmid⟩
            · rw [hbefore] at h
              cases h
            · exact Or.inr ⟨hC.trans hmid, Or.inr (hL.trans hlow)⟩
          | orGate =>
            simp only [reduceCtorEq, ite_false] at hinputs
            rcases hinputs with hlow | hmid | h
            · exact Or.inl ⟨rfl, hL.trans hlow⟩
            · exact Or.inr ⟨hC.trans hmid, Or.inl rfl⟩
            · rw [hbefore] at h
              cases h
        have hc := l.encodedSegments_core_east_from_frame p hl hM ha relay hg hk hmid
          (by change g.internal + 1 < (state.internal.set (g.internal + 2) true).length; simp only [List.length_set]; omega)
          hh haccess B hB
        have heq : ShuttleMacro.withShort relay g.internal true =
            {state with internal := g.canonicalUpdate state.internal g.right false} := by
          change SignalState.mk state.axes ((state.internal.set (g.internal + 2) true).set (g.internal + 1) true) = _
          simp only [Placement.canonicalUpdate, hleft, ite_false, hk, Option.isSome_some, and_self, ite_true, Bool.not_false]
          rw [List.set_comm true true (by omega)]
        rw [heq] at hc
        exact hr.trans hc
      · simp only [ite_true] at hphase
        let short := ShuttleMacro.withShort state g.internal false
        have hc := l.encodedSegments_core_west_from_frame p hl hM ha state hg hk hmid (by omega) hH hR B hB
        have hrbefore : short.internal.getD (g.internal + 2) false = !false := by
          rw [ShuttleMacro.withShort_other state g.internal false (g.internal + 2) (by omega), hR]
          rfl
        have hrstand : short.axes.getD g.right false = false := by
          change state.axes.getD g.right false = false
          simpa only [hphase, Bool.not_true] using hbefore
        have hr := l.encodedSegments_gate_right_from_frame p hl hM ha short hg hk
          (by change g.internal + 2 < (state.internal.set (g.internal + 1) false).length; simpa only [List.length_set] using hi)
          false hrbefore hrstand B hB
        have heq : {short with internal := short.internal.set (g.internal + 2) false} =
            {state with internal := g.canonicalUpdate state.internal g.right true} := by
          simp only [Placement.canonicalUpdate, hleft, ite_false, hk, Option.isSome_some, and_self, ite_true, Bool.not_true]
          rfl
        rw [heq] at hr
        exact hc.trans hr
    · have hupdate : g.canonicalUpdate state.internal port gain = state.internal := by
        simp only [Placement.canonicalUpdate, hleft, ite_false, hheavy, and_false]
      rw [hupdate]

/-- An actual group's old canonical slots align to the new interface bit at its losing/gaining phase. -/
theorem encodedSegments_canonical_group_from_frame (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (axes : List Bool) (hlegal : l.InputLegal axes) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {port : ℕ} (gain : Bool)
    (hbefore : axes.getD port false = !gain)
    (hphase : state.axes = if g.side = .upper then (if gain then axes.set port gain else axes)
      else (if gain then axes else axes.set port gain))
    (hlen : state.internal.length = (l.canonical axes).internal.length)
    (hread : ∀ j < (if g.gate.isSome then 3 else 1),
      state.internal.getD (g.internal + j) false = (l.canonical axes).internal.getD (g.internal + j) false)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Reachable B none (l.cornerState p state).toState
      (l.cornerState p {state with internal := g.canonicalUpdate state.internal port gain}).toState := by
  have hb := l.canonical_placement_bounds axes hg
  rw [← hlen] at hb
  cases hk : g.gate with
  | none =>
    have hread0 := hread 0 (by simp only [hk, Option.isSome_none, Bool.false_eq_true, ite_false]; omega)
    simp only [Nat.add_zero] at hread0
    apply l.encodedSegments_wire_canonicalUpdate_from_frame p hl hM ha axes hlegal state hg hk gain hbefore hphase _ hread0 B hB
    simp only [hk, Option.isSome_none, Bool.false_eq_true, ite_false] at hb
    omega
  | some kind =>
    have hs := (placement_gate_shape l hg hk).1
    have hc := l.canonical_gate_read axes hg hk
    have hread0 := (hread 0 (by simp only [hk, Option.isSome_some, ite_true]; omega)).trans hc.1
    have hread1 := (hread 1 (by simp only [hk, Option.isSome_some, ite_true]; omega)).trans hc.2.1
    have hread2 := (hread 2 (by simp only [hk, Option.isSome_some, ite_true]; omega)).trans hc.2.2
    apply l.encodedSegments_gate_canonicalUpdate_from_frame p hl hM ha axes hlegal state hg hk gain hbefore
      (by simpa only [hs, reduceCtorEq, ite_false] using hphase) _ ⟨hread0, hread1, hread2⟩ B hB
    simp only [hk, Option.isSome_some, ite_true] at hb
    omega

end PushPuzzle.PushS.PortLayout
