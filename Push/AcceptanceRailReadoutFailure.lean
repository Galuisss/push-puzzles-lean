/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisReadoutFailure
import all PushS.PortOrdinaryFailureOnset
import all PushS.PortWireTrains
import all PushS.PortGateIndexing

/-! Actual ordinary and gate rail motions preserve endpoint faults and locate their onset. -/

public section
namespace PushPuzzle.Push.AcceptanceAxisReadout

open PushFS PushS PushS.PortLayout

/-- The actual shared horizontal train motions across one physical step. -/
structure RailMotions (l : PortLayout) (p : Scales.Parameters) (B : Board (p.W + 1) (p.H + 1))
    (u v : State (p.W + 1) (p.H + 1)) : Prop where
  wire : ∀ g, g ∈ placements l → g.gate = none → Nonempty (WireTrainStep p g B u v)
  gate : ∀ g, g ∈ placements l → ∀ kind, g.gate = some kind →
    ∃ before after, GateTrainMotion p g kind u v before after

section Motion
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (haxes : l.portCount ≤ p.axes) {B : Board (p.W + 1) (p.H + 1)}
  {u v : State (p.W + 1) (p.H + 1)} (motions : RailMotions l p B u v)
  (e : Endpoint) (he : e ∈ l.endpoints)

include hl haxes motions he

/-- A failed horizontal supply persists through genuine rail motion from outside its pocket. -/
theorem endpoint_horizontal_failure_step_of_motions {horizontal : ℕ}
    (word : EndpointHorizontalReadout p e u horizontal) (failed : horizontal ≤ 1)
    (outside : u.player ∉ ordinaryPocket p e) :
    ∃ nextHorizontal, EndpointHorizontalReadout p e v nextHorizontal ∧ nextHorizontal ≤ 1 := by
  obtain ⟨g, hg, hend⟩ := List.mem_flatMap.mp he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hend
  cases hk : g.gate with
  | none =>
    obtain ⟨motion⟩ := motions.wire g hg hk
    have source := motion.source_shape.readout motion.marked.length_pos
    have target := motion.target_shape.readout motion.marked.length_pos
    simp only [hk, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] at hend
    rcases hend with rfl | rfl
    · have hs := source.left_endpoint hl hg hk
      have hv := target.left_endpoint hl hg hk
      have hb := (l.endpoint_horizontal_failed_iff p hl haxes he word hs).mp failed
      exact ⟨_, hv, motion.left_fault_preserved hb outside⟩
    · have hs := source.right_endpoint hl hg hk
      have hv := target.right_endpoint hl hg hk
      have hb := (l.endpoint_horizontal_failed_iff p hl haxes he word hs).mp failed
      exact ⟨_, hv, motion.right_fault_preserved hb outside⟩
  | some kind =>
    obtain ⟨before, after, motion⟩ := motions.gate g hg kind hk
    have hside := (placement_gate_shape l hg hk).1
    have hlevel := gate_level_one l hg hk
    simp only [hk, Option.isSome_some, ite_true] at hend
    rcases hend with rfl | rfl
    · have hs := motion.before_shape.left_endpoint hl hg hk
      have hv := motion.after_shape.left_endpoint hl hg hk
      have hb := (l.endpoint_horizontal_failed_iff p hl haxes he word hs).mp failed
      exact ⟨_, hv, motion.left_wire_fault_preserved hside hlevel hb outside⟩
    · have hs := motion.before_shape.right_endpoint hl hg hk
      have hv := motion.after_shape.right_endpoint hl hg hk
      have hb := (l.endpoint_horizontal_failed_iff p hl haxes he word hs).mp failed
      exact ⟨_, hv, motion.right_wire_fault_preserved hside hlevel hb outside⟩

/-- A real loss of horizontal supply leaves the next player outside that endpoint's physical pocket. -/
theorem endpoint_horizontal_loss_outside_of_motions {beforeHorizontal afterHorizontal : ℕ}
    (source : EndpointHorizontalReadout p e u beforeHorizontal)
    (target : EndpointHorizontalReadout p e v afterHorizontal)
    (beforeSupplied : 2 ≤ beforeHorizontal) (afterFailed : afterHorizontal ≤ 1)
    {d : Direction} (adjacent : Adjacent d u.player v.player) : v.player ∉ ordinaryPocket p e := by
  obtain ⟨g, hg, hend⟩ := List.mem_flatMap.mp he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hend
  cases hk : g.gate with
  | none =>
    obtain ⟨motion⟩ := motions.wire g hg hk
    have span := wire_train_margin l p hl hg hk
    have hs := motion.source_shape.readout motion.marked.length_pos
    have hv := motion.target_shape.readout motion.marked.length_pos
    simp only [hk, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] at hend
    rcases hend with rfl | rfl
    · have hsrc := l.endpoint_horizontal_failed_iff p hl haxes he source (hs.left_endpoint hl hg hk)
      have htgt := l.endpoint_horizontal_failed_iff p hl haxes he target (hv.left_endpoint hl hg hk)
      exact wire_left_loss motion span (by omega) (htgt.mp afterFailed) adjacent
    · have hsrc := l.endpoint_horizontal_failed_iff p hl haxes he source (hs.right_endpoint hl hg hk)
      have htgt := l.endpoint_horizontal_failed_iff p hl haxes he target (hv.right_endpoint hl hg hk)
      exact wire_right_loss motion span (by omega) (htgt.mp afterFailed) adjacent
  | some kind =>
    obtain ⟨before, after, motion⟩ := motions.gate g hg kind hk
    simp only [hk, Option.isSome_some, ite_true] at hend
    rcases hend with rfl | rfl
    · have hsrc := l.endpoint_horizontal_failed_iff p hl haxes he source (motion.before_shape.left_endpoint hl hg hk)
      have htgt := l.endpoint_horizontal_failed_iff p hl haxes he target (motion.after_shape.left_endpoint hl hg hk)
      exact gate_left_loss motion (by omega) (htgt.mp afterFailed) adjacent
    · have hsrc := l.endpoint_horizontal_failed_iff p hl haxes he source (motion.before_shape.right_endpoint hl hg hk)
      have htgt := l.endpoint_horizontal_failed_iff p hl haxes he target (motion.after_shape.right_endpoint hl hg hk)
      exact gate_right_loss motion (by omega) (htgt.mp afterFailed) adjacent

end Motion
end PushPuzzle.Push.AcceptanceAxisReadout
