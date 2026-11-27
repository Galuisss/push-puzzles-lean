/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateSampleZero
import all PushS.PortCoreCrossing
import all PushS.PortSegments

/-! All eight actual terminal work-row samples supply the signed shuttle readout certificate. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])
  {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
  {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hg hk hu hsu hp

/-- Every one of the eight signed canonical target probes is an actual terminal work-row hole. -/
private theorem canonical_gate_sample_terminal {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - readDepth p 1) {x : ℤ}
    (hx : (q.1.val : ℤ) - p.x (g.left + 1) = x) (hprobe : x ∈ Shuttle.probes)
    (hhole : (canonicalShuttleTarget l target g).placement.hole kind x) : q ∈ holes t := by
  by_cases hzero : x = 0
  · exact canonical_gate_zero_sample_terminal l p hl hM haxes initial target hgate hg hk hu hsu hp hr accepted
      (by omega) hy (canonicalShuttleTarget_hole_target l p target hg hk hy hx hhole)
  · exact canonical_gate_nonzero_sample_terminal l p hl hM haxes initial target hgate hg hk hr accepted hy hx hprobe hzero hhole

/-- The complete actual accepted terminal sampling certificate is exactly `Shuttle.Samples`. -/
theorem canonical_gate_shuttle_samples {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {b : ThreeBlocks} (shape : GateRailBlocks p g kind t b) :
    Shuttle.Samples kind (canonicalShuttleTarget l target g) (gateTrainPlacement p g b) := by
  intro x hprobe hhole
  have hb : -2 ≤ x ∧ x ≤ 12 := by
    simp only [Shuttle.probes, Finset.mem_insert, Finset.mem_singleton] at hprobe
    omega
  have hmiddle : g.left + 1 < p.axes := by
    rw [← hp]
    exact (l.endpoints_port_lt hl hu).trans_le haxes
  have hx0 := readLength_add_lt_x p (g.left + 1) 0
  have hxW := x_add_readLength_lt_W p hmiddle 0
  have hY := readDepth_ge p le_rfl p.levels_pos
  have hYH := readDepth_add_lt_H p 1
  have hcoord : (((p.x (g.left + 1) : ℤ) + x).toNat : ℤ) = (p.x (g.left + 1) : ℤ) + x :=
    Int.toNat_of_nonneg (by omega)
  let q : Cell (p.W + 1) (p.H + 1) :=
    (⟨((p.x (g.left + 1) : ℤ) + x).toNat, by omega⟩, ⟨p.H - readDepth p 1, by omega⟩)
  have hqx : (q.1.val : ℤ) - p.x (g.left + 1) = x := by dsimp only [q]; omega
  have hphysical := canonical_gate_sample_terminal l p hl hM haxes initial target hgate hg hk hu hsu hp
    hr accepted (q := q) rfl hqx hprobe hhole
  have hactual := (shape.core_hole (placement_gate_shape l hg hk).2 (q := q) rfl (by omega)).mp hphysical
  simpa only [hqx] using hactual

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
