/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortCanonicalAccess
public import PushS.PortOrdinaryFrameMacro
import all PushS.PortCanonicalUpdate
import all PushS.PortAxisGroups
import all PushS.PortGateIndexing
import all PushS.PortWireIndexing
import all PushS.PortCoreCrossing
import all PushS.PortSegments

/-! The actual interface-axis push after withdrawing the old losing-page internal signals. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction

/-- Canonical source bits with only the old losing-page group's affected internals withdrawn. -/
@[expose] def AxisGroups.prepared {l : PortLayout} {port : ℕ} (groups : l.AxisGroups port)
    (axes : List Bool) (gain : Bool) : SignalState :=
  ⟨axes, (if gain then groups.lower else groups.upper).canonicalUpdate (l.canonical axes).internal port gain⟩

private theorem prepared_receiving (l : PortLayout) (axes : List Bool) (hlegal : l.InputLegal axes)
    {port : ℕ} (groups : l.AxisGroups port) (gain : Bool) (hbefore : axes.getD port false = !gain)
    {e : Endpoint} (he : e ∈ l.endpoints) (hs : e.side = if gain then .upper else .lower) (hp : e.port = port) :
    (if e.inward then (groups.prepared axes gain).internal.getD e.internal false
      else !((groups.prepared axes gain).internal.getD e.internal false)) = true := by
  have haxis : (if e.side = .upper then axes.getD e.port false else !(axes.getD e.port false)) = false := by
    cases gain <;> simp only [hp, hs, hbefore, Bool.false_eq_true, ite_false, ite_true,
      reduceCtorEq, Bool.not_true, Bool.not_false]
  have hc := l.canonical_endpoint_receiving axes hlegal he haxis
  have hread : (groups.prepared axes gain).internal.getD e.internal false = (l.canonical axes).internal.getD e.internal false := by
    cases gain
    · apply l.canonicalUpdate_endpoint_otherSide groups.upper_mem he
      simp only [groups.upper_side, hs, Bool.false_eq_true, ite_false]
      intro h
      cases h
    · apply l.canonicalUpdate_endpoint_otherSide groups.lower_mem he
      simp only [groups.lower_side, hs, ite_true]
      intro h
      cases h
  rw [hread]
  exact hc

/-- The prepared canonical state performs its real ordinary or middle-core axis push and returns to the frame. -/
theorem encodedSegments_prepared_axis_from_frame (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (axes : List Bool) (hlegal : l.InputLegal axes) {port : ℕ} (hp : port < axes.length)
    (groups : l.AxisGroups port) (gain : Bool) (hbefore : axes.getD port false = !gain)
    (hnew : l.OrderedInputs (axes.set port gain))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Reachable B none (l.cornerState p (groups.prepared axes gain)).toState
      (l.cornerState p {groups.prepared axes gain with axes := axes.set port gain}).toState := by
  obtain ⟨upper, hu, hus, hup, _⟩ := placement_outer_endpoint l groups.upper_mem groups.upper_port
  have hsu : upper.side = .upper := hus.trans groups.upper_side
  have ordinary (lower : Endpoint) (hlow : lower ∈ l.endpoints) (hsl : lower.side = .lower)
      (hlp : lower.port = port) := by
    have hstand : (if gain then
        (if upper.inward then (groups.prepared axes gain).internal.getD upper.internal false
          else !((groups.prepared axes gain).internal.getD upper.internal false))
      else (if lower.inward then (groups.prepared axes gain).internal.getD lower.internal false
          else !((groups.prepared axes gain).internal.getD lower.internal false))) = true := by
      cases gain
      · exact prepared_receiving l axes hlegal groups false hbefore hlow hsl hlp
      · exact prepared_receiving l axes hlegal groups true hbefore hu hsu hup
    have hm := l.encodedSegments_axis_from_frame p hl hM ha (groups.prepared axes gain) upper lower hu hlow hsu hsl
      (hlp.trans hup.symm) (by change upper.port < axes.length; simpa only [hup] using hp) gain
      (by change axes.getD upper.port false = !gain; simpa only [hup] using hbefore) hstand B hB
    simpa only [hup] using hm
  rcases groups.lower_port with hleft | hright | ⟨hgate, hmid⟩
  · obtain ⟨lower, hlow, hls, hlp, _⟩ := placement_outer_endpoint l groups.lower_mem (Or.inl hleft)
    exact ordinary lower hlow (hls.trans groups.lower_side) hlp
  · obtain ⟨lower, hlow, hls, hlp, _⟩ := placement_outer_endpoint l groups.lower_mem (Or.inr hright)
    exact ordinary lower hlow (hls.trans groups.lower_side) hlp
  · cases hk : groups.lower.gate with
    | none => simp only [hk, Option.isSome_none, Bool.false_eq_true] at hgate
    | some kind =>
      have hne : groups.upper ≠ groups.lower := by
        intro h
        have hs := groups.upper_side.symm.trans ((congrArg Placement.side h).trans groups.lower_side)
        cases hs
      have hstand : if gain then
          (if upper.inward then (groups.prepared axes gain).internal.getD upper.internal false
            else !((groups.prepared axes gain).internal.getD upper.internal false)) = true
        else ((groups.prepared axes gain).internal.getD (groups.lower.internal + 1) false = true ∧
            (kind = .orGate ∨ (groups.prepared axes gain).internal.getD groups.lower.internal false = false)) ∨
          (kind = .orGate ∧ (groups.prepared axes gain).internal.getD groups.lower.internal false = false) := by
        cases gain
        · simp only [Bool.false_eq_true, ite_false]
          have hs := l.canonical_gate_read axes groups.lower_mem hk
          have hread0 : (groups.prepared axes false).internal.getD groups.lower.internal false = axes.getD groups.lower.left false := by
            exact (canonicalUpdate_other l groups.upper_mem groups.lower_mem hne _ port false
              (j := 0) (by simp only [hk, Option.isSome_some, ite_true]; omega)).trans hs.1
          have hread1 : (groups.prepared axes false).internal.getD (groups.lower.internal + 1) false = !(axes.getD groups.lower.right false) := by
            exact (canonicalUpdate_other l groups.upper_mem groups.lower_mem hne _ port false
              (j := 1) (by simp only [hk, Option.isSome_some, ite_true]; omega)).trans hs.2.1
          have hinputs := hlegal.gate_inputs groups.lower_mem hk
          have hmidold : axes.getD (groups.lower.left + 1) false = true := by
            simpa only [hmid, Bool.not_false] using hbefore
          cases kind with
          | andGate =>
            simp only [ite_true] at hinputs
            have hheavy : axes.getD groups.lower.right false = false := hinputs.resolve_right (by
              rintro ⟨_, hc⟩
              rw [hmidold] at hc
              cases hc)
            have horder := hnew.gate_order groups.lower_mem hk
            have hmidnew : (axes.set port false).getD (groups.lower.left + 1) false = false := by
              rw [← hmid]
              exact List.getD_set_self hp
            have hleftnew := horder hmidnew
            rw [List.getD_set_ne (by omega)] at hleftnew
            exact Or.inl ⟨by rw [hread1, hheavy]; rfl, Or.inr (hread0.trans hleftnew)⟩
          | orGate =>
            simp only [reduceCtorEq, ite_false] at hinputs
            rcases hinputs with hleft | hc | hheavy
            · exact Or.inr ⟨rfl, hread0.trans hleft⟩
            · rw [hmidold] at hc
              cases hc
            · exact Or.inl ⟨by rw [hread1, hheavy]; rfl, Or.inl rfl⟩
        · exact prepared_receiving l axes hlegal groups true hbefore hu hsu hup
      have hm := l.encodedSegments_gate_axis_from_frame p hl hM ha (groups.prepared axes gain) groups.lower_mem hk
        hu hsu (hup.trans hmid) gain (by change groups.lower.left + 1 < axes.length; simpa only [hmid] using hp)
        (by change axes.getD (groups.lower.left + 1) false = !gain; simpa only [hmid] using hbefore) hstand B hB
      simpa only [show (groups.prepared axes gain).axes = axes from rfl, ← hmid] using hm

end PushPuzzle.PushS.PortLayout
