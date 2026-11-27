/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortCanonicalUpdate
import all PushS.PortCanonicalUpdate
import all PushS.PortGateIndexing
import all PushS.PortWireIndexing
import all PushS.PortCoreCrossing
import all PushS.PortSegments

/-! Canonical receiving endpoints and the unaffected opposite-page actuator. -/

public section
namespace PushPuzzle.PushS.PortLayout


/-- A canonical ordinary endpoint without its axis input receives its horizontal input. -/
theorem canonical_endpoint_receiving (l : PortLayout) (axes : List Bool) (hlegal : l.InputLegal axes)
    {e : Endpoint} (he : e ∈ l.endpoints)
    (haxis : (if e.side = .upper then axes.getD e.port false else !(axes.getD e.port false)) = false) :
    (if e.inward then (l.canonical axes).internal.getD e.internal false
      else !((l.canonical axes).internal.getD e.internal false)) = true := by
  obtain ⟨g, hg, he⟩ := List.mem_flatMap.mp he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  cases hk : g.gate with
  | none =>
    have hslot := l.canonical_wire_read axes hg hk
    have hinputs := hlegal.wire_inputs hg hk
    simp only [hk, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] at he
    rcases he with rfl | rfl
    · simp only [ite_true]
      rw [hslot]
      cases hs : g.side with
      | upper => simpa only [hs, ite_true, Bool.not_false] using congrArg Bool.not haxis
      | lower =>
        simpa only [hs, reduceCtorEq, ite_false, Bool.not_eq_false_eq_eq_true] using haxis
    · simp only [Bool.false_eq_true, ite_false]
      rw [hslot]
      cases hs : g.side with
      | upper =>
        simp only [hs, ite_true] at haxis hinputs ⊢
        have hleft := hinputs.resolve_right (by intro h; rw [haxis] at h; cases h)
        simp only [hleft, Bool.not_not]
      | lower =>
        simp only [hs, reduceCtorEq, ite_false, Bool.not_eq_false_eq_eq_true] at haxis hinputs ⊢
        have hleft := hinputs.resolve_right (by intro h; rw [haxis] at h; cases h)
        simp only [hleft, Bool.not_false]
  | some kind =>
    have hs := (placement_gate_shape l hg hk).1
    have hslot := l.canonical_gate_read axes hg hk
    simp only [hk, Option.isSome_some, ite_true] at he
    rcases he with rfl | rfl
    · simp only [hs, reduceCtorEq, ite_false, Bool.not_eq_false_eq_eq_true] at haxis
      simpa only [ite_true, hslot.1] using haxis
    · simp only [hs, reduceCtorEq, ite_false, Bool.not_eq_false_eq_eq_true] at haxis
      simpa only [Bool.false_eq_true, ite_false, hslot.2.2, Bool.not_not] using haxis

/-- Updating one actual group's canonical internal bits preserves every opposite-page endpoint read. -/
theorem canonicalUpdate_endpoint_otherSide (l : PortLayout) {g : Placement}
    (hg : g ∈ placements l) {e : Endpoint} (he : e ∈ l.endpoints) (hs : g.side ≠ e.side)
    (bits : List Bool) (port : ℕ) (gain : Bool) :
    (g.canonicalUpdate bits port gain).getD e.internal false = bits.getD e.internal false := by
  obtain ⟨h, hh, he⟩ := List.mem_flatMap.mp he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · have hne : g ≠ h := fun heq => hs (congrArg Placement.side heq)
    simpa only [Nat.add_zero] using canonicalUpdate_other l hg hh hne bits port gain
      (j := 0) (by split <;> omega)
  · have hne : g ≠ h := fun heq => hs (congrArg Placement.side heq)
    apply canonicalUpdate_other l hg hh hne bits port gain
    cases h.gate <;> simp only [Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ite_false, ite_true] <;> omega

end PushPuzzle.PushS.PortLayout
