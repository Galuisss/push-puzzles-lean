/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisReadoutTrain
public import PushS.PortOrdinaryFailureOnset
import all PushS.PortOrdinaryFailureOnset
import all PushS.PortAxisGroups

/-! Ordinary endpoint axis faults persist and arise outside their pocket under actual shared train motions. -/

public section
namespace PushPuzzle.Push.AcceptanceAxisReadout

open PushFS PushS PushS.PortLayout

section Motion
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
  {u v : State (p.W + 1) (p.H + 1)} (motions : AxisMotions l p u v)
  (e : Endpoint) (he : e ∈ l.endpoints)

include hl hM haxes motions he

/-- A failed ordinary axis supply persists while the player stays outside its physical pocket. -/
theorem endpoint_axis_failure_step_of_motions {parameter shift : ℕ}
    (word : EndpointAxisReadout p e u parameter shift) (failed : 2 ≤ parameter)
    (outside : u.player ∉ ordinaryPocket p e) :
    ∃ nextParameter nextShift, EndpointAxisReadout p e v nextParameter nextShift ∧ 2 ≤ nextParameter := by
  cases hs : e.side with
  | lower =>
    obtain ⟨upper, hu, hsu, hp⟩ := l.endpoints_upper_exists hl (l.endpoints_port_lt hl he)
    obtain ⟨before, after, motion⟩ := motions.ordinary upper e hu he hsu hs hp.symm
    have source := motion.before_readout.lower_endpoint hs hp.symm
    have target := motion.after_readout.lower_endpoint hs hp.symm
    have eq := l.endpoint_axis_parameter_unique p hl hM haxes he word source
    exact ⟨_, _, target, motion.lower_fault_preserved hs hp.symm (by rwa [← eq]) outside⟩
  | upper =>
    obtain ⟨groups⟩ := l.axisGroups_nonempty hl (l.endpoints_port_lt hl he)
    have ordinary (hk : e.port = groups.lower.left ∨ e.port = groups.lower.right) :
        ∃ nextParameter nextShift, EndpointAxisReadout p e v nextParameter nextShift ∧ 2 ≤ nextParameter := by
      obtain ⟨lower, hlow, hls, hlp, _⟩ := placement_outer_endpoint l groups.lower_mem hk
      obtain ⟨before, after, motion⟩ := motions.ordinary e lower he hlow hs (hls.trans groups.lower_side) hlp
      have source := motion.before_readout.upper_endpoint hs
      have target := motion.after_readout.upper_endpoint hs
      have eq := l.endpoint_axis_parameter_unique p hl hM haxes he word source
      exact ⟨_, _, target, motion.upper_fault_preserved hs (by rwa [← eq]) outside⟩
    rcases groups.lower_port with hleft | hright | ⟨hgate, hmid⟩
    · exact ordinary (Or.inl hleft)
    · exact ordinary (Or.inr hright)
    · cases hk : groups.lower.gate with
      | none => simp only [hk, Option.isSome_none, Bool.false_eq_true] at hgate
      | some kind =>
        obtain ⟨before, after, motion⟩ := motions.gate groups.lower groups.lower_mem kind hk e he hs hmid
        have source := (gate_readout_of_shape motion.before_shape motion.before_positive).upper_endpoint hs hmid
        have target := (gate_readout_of_shape motion.after_shape motion.after_positive).upper_endpoint hs hmid
        have eq := l.endpoint_axis_parameter_unique p hl hM haxes he word source
        exact ⟨_, _, target, motion.upper_fault_preserved hs hmid (by rwa [← eq]) outside⟩

/-- A real loss of axis supply leaves the next player outside that ordinary endpoint's pocket. -/
theorem endpoint_axis_loss_outside_of_motions {beforeParameter beforeShift afterParameter afterShift : ℕ}
    (source : EndpointAxisReadout p e u beforeParameter beforeShift)
    (target : EndpointAxisReadout p e v afterParameter afterShift)
    (beforeSupplied : beforeParameter ≤ 1) (afterFailed : 2 ≤ afterParameter)
    {d : Direction} (adjacent : Adjacent d u.player v.player) : v.player ∉ ordinaryPocket p e := by
  have hY := readDepth_ge p (l.endpoints_level_bounds p hl hM he).1 (l.endpoints_level_bounds p hl hM he).2
  cases hs : e.side with
  | lower =>
    obtain ⟨upper, hu, hsu, hp⟩ := l.endpoints_upper_exists hl (l.endpoints_port_lt hl he)
    obtain ⟨before, after, motion⟩ := motions.ordinary upper e hu he hsu hs hp.symm
    have hsrc := l.endpoint_axis_parameter_unique p hl hM haxes he source (motion.before_readout.lower_endpoint hs hp.symm)
    have htgt := l.endpoint_axis_parameter_unique p hl hM haxes he target (motion.after_readout.lower_endpoint hs hp.symm)
    exact ordinary_lower_loss motion hs (by omega) (by rwa [← hsrc]) (by rwa [← htgt]) adjacent
  | upper =>
    obtain ⟨groups⟩ := l.axisGroups_nonempty hl (l.endpoints_port_lt hl he)
    have ordinary (hk : e.port = groups.lower.left ∨ e.port = groups.lower.right) : v.player ∉ ordinaryPocket p e := by
      obtain ⟨lower, hlow, hls, hlp, _⟩ := placement_outer_endpoint l groups.lower_mem hk
      obtain ⟨before, after, motion⟩ := motions.ordinary e lower he hlow hs (hls.trans groups.lower_side) hlp
      have hsrc := l.endpoint_axis_parameter_unique p hl hM haxes he source (motion.before_readout.upper_endpoint hs)
      have htgt := l.endpoint_axis_parameter_unique p hl hM haxes he target (motion.after_readout.upper_endpoint hs)
      exact ordinary_upper_loss motion hs (by omega) (by rwa [← hsrc]) (by rwa [← htgt]) adjacent
    rcases groups.lower_port with hleft | hright | ⟨hgate, hmid⟩
    · exact ordinary (Or.inl hleft)
    · exact ordinary (Or.inr hright)
    · cases hk : groups.lower.gate with
      | none => simp only [hk, Option.isSome_none, Bool.false_eq_true] at hgate
      | some kind =>
        obtain ⟨before, after, motion⟩ := motions.gate groups.lower groups.lower_mem kind hk e he hs hmid
        have hsrc := l.endpoint_axis_parameter_unique p hl hM haxes he source
          ((gate_readout_of_shape motion.before_shape motion.before_positive).upper_endpoint hs hmid)
        have htgt := l.endpoint_axis_parameter_unique p hl hM haxes he target
          ((gate_readout_of_shape motion.after_shape motion.after_positive).upper_endpoint hs hmid)
        exact gate_upper_loss motion hs (by omega) (by rwa [← hsrc]) (by rwa [← htgt]) adjacent

end Motion
end PushPuzzle.Push.AcceptanceAxisReadout
