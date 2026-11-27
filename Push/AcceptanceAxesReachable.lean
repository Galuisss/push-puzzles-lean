/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptancePhysicalFaultExclusions
public import Push.AcceptanceDecodedLegalStep
public import Push.AcceptanceAxisReadoutTrace

/-! The actual accepted reader programme projects to the original legal axis path with no residual inventory contracts. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram AcceptanceAxisReadout AcceptanceDecodedInputs

private theorem propagate {α : Type} {P : α → Prop} {a b : α}
    (path : Relation.ReflTransGen (fun x y => P x → P y) a b) (base : P a) : P b := by
  induction path with
  | refl => exact base
  | tail _ step ih => exact step ih

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) (hpartners : Partner.ReaderPartners l)
  (hstart : l.InputLegal initial) (hgoal : l.InputLegal target)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hpartners hstart hgoal

/-- Every decoded actual prefix of an accepted repaired source satisfies its original native input constraints. -/
private theorem canonical_axisReadout_legal {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {axes : List Bool} (decoded : l.AxisReadout p u axes) : l.InputLegal axes := by
  let Inv (s : State (p.W + 1) (p.H + 1)) := ∀ axes, l.AxisReadout p s axes → l.InputLegal axes
  have dynamics := canonical_physical_dynamics l p hl hM haxes initial target hgate hpartners hgoal (hsu.trans hut) accepted
  have base : Inv (I).initial := by
    intro axes word
    rw [l.canonicalInstance_decoded_initial p hl hM haxes initial target hstart.axes_length word]
    exact hstart
  have path : Relation.ReflTransGen (fun a b => Inv a → Inv b) (I).initial u := by
    apply Path.enrich hsu
    intro a b hsa step hbu legal next word
    have hbt := hbu.trans hut
    obtain ⟨before, beforeWord⟩ := canonical_axis_readout_exists l p hl hM haxes initial target hgate hpartners
      hsa ((Relation.ReflTransGen.single step).trans hbt) accepted
    apply decoded_legal_step_of_motions l p hl hM haxes step (dynamics.axis hsa step hbt)
      (dynamics.rail hsa step hbt) beforeWord word (legal before beforeWord)
    · intro e he
      rintro ⟨fault⟩
      exact canonical_endpoint_fault_impossible l p hl hM haxes initial target hgate hpartners hgoal e he
        (hsa.tail step) hbt accepted fault
    · intro g hg kind hk upper hu hs hp
      exact canonical_gate_fault_exclusions l p hl hM haxes initial target hgate hpartners hgoal hg hk hu hs hp
        (hsa.tail step) hbt accepted
  exact propagate (P := Inv) path base axes decoded

/-- All complete actual readouts on an accepted source run form a genuine trace to the original target word. -/
private theorem canonical_axis_trace {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    TraceReadout l p (I).board (I).initial t initial target := by
  have dynamics := canonical_physical_dynamics l p hl hM haxes initial target hgate hpartners hgoal hr accepted
  constructor
  · intro u hsu hut
    exact canonical_axis_readout_exists l p hl hM haxes initial target hgate hpartners hsu hut accepted
  · intro axes word
    exact l.canonicalInstance_decoded_initial p hl hM haxes initial target hstart.axes_length word
  · intro axes word
    exact word.unique hl (canonical_terminal_axis_readout l p hl hM haxes initial target hgate hpartners hgoal.axes_length hr accepted)
  · intro u v hsu step hvt axes next source targetReadout
    have legal := canonical_axisReadout_legal l p hl hM haxes initial target hgate hpartners hstart hgoal
      hsu ((Relation.ReflTransGen.single step).trans hvt) accepted source
    apply decoded_axis_step_of_faults l p hl hM haxes step (dynamics.axis hsu step hvt)
      (dynamics.rail hsu step hvt) source targetReadout legal
    · intro e he
      rintro ⟨fault⟩
      exact canonical_endpoint_fault_impossible l p hl hM haxes initial target hgate hpartners hgoal e he
        (hsu.tail step) hvt accepted fault
    · intro g hg kind hk upper hu hs hp
      exact canonical_gate_fault_exclusions l p hl hM haxes initial target hgate hpartners hgoal hg hk hu hs hp
        (hsu.tail step) hvt accepted

/-- A real accepted repaired source trajectory gives the complete initial-to-target legal original axis path. -/
theorem canonical_axes_reachable {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Relation.ReflTransGen l.AxisStep initial target :=
  (canonical_axis_trace l p hl hM haxes initial target hgate hpartners hstart hgoal hr accepted).reachable hr

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
