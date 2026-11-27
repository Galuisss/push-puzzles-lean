/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortDecodedInputs
import all PushS.PortGateIndexing

/-! The existing native input legality is preserved by every real step of a successful wall-free storage solution. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial : SignalState)
  (targetAxes : List Bool) (hlegal : l.InputLegal targetAxes)

local notation "I" => l.physicalInstance p hl hM ha initial (l.canonical targetAxes)

include hlegal

/-- Every actual successful step preserves the complete native input legality of its decoded axis array. -/
theorem physicalInstance_decoded_legal_step {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {axes next : List Bool} (source : l.AxisReadout p u axes) (targetReadout : l.AxisReadout p v next)
    (hsource : l.InputLegal axes) : l.InputLegal next := by
  apply InputLegal.of_placements l next targetReadout.axes_length
  · intro g hg hw
    exact l.physicalInstance_decoded_wire_inputs p hl hM ha initial targetAxes hlegal hg hw (hsu.tail hm) hvt ht targetReadout
  · intro g hg kind hk
    have hports := gate_port_bounds l hl hg hk
    have hshape := placement_gate_shape l hg hk
    have hmid : g.left + 1 < l.portCount := by omega
    obtain ⟨upper, hu, hside, hp⟩ := l.endpoints_upper_exists hl hmid
    obtain ⟨before, hb⟩ := l.physicalInstance_gate_group_readout p hl hM ha initial (l.canonical targetAxes)
      hg hk hu hside hp hsu ((Relation.ReflTransGen.single hm).trans hvt) ht
    obtain ⟨after, hc⟩ := l.physicalInstance_gate_group_readout p hl hM ha initial (l.canonical targetAxes)
      hg hk hu hside hp (hsu.tail hm) hvt ht
    have hbefore := (l.physicalInstance_decoded_gate_inputs_iff p hl hM ha initial (l.canonical targetAxes)
      hg hk hu hside hp hsu ((Relation.ReflTransGen.single hm).trans hvt) ht source hb).mpr (hsource.gate_inputs hg hk)
    have hafter := l.physicalInstance_gate_group_legal_step p hl hM ha initial targetAxes hlegal
      hg hk hu hside hp hsu hm hvt ht hb hc hbefore
    exact (l.physicalInstance_decoded_gate_inputs_iff p hl hM ha initial (l.canonical targetAxes)
      hg hk hu hside hp (hsu.tail hm) hvt ht targetReadout hc).mp hafter

end Solution
end PushPuzzle.PushS.PortLayout
