/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProbeCancellation
public import Push.AcceptanceSoundnessProbeLocation
public import Push.AcceptanceSoundnessGateProbeLocation
public import Push.AcceptanceSoundnessWireAxisNoInput
import all Push.AcceptanceProbePartners
import all PushS.PortSegments
import all PushS.PortEndpointEnumeration

/-! Actual probe observations and inventory errors indexed by the original finite port set. -/

public section
namespace PushPuzzle.Push.AcceptanceProbeNumerics

open PushFS PushS PushS.PortLayout AcceptanceProgram AcceptanceSoundness

/-- The actual pre-probe residual after the literal first thirteen programme rounds. -/
@[expose] def residual (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    (t : State (p.W + 1) (p.H + 1)) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
    (targetHoles l p target) (PushS.holes t) 13

/-- The real residual point stock on this port's allocated upper probe row. -/
@[expose] noncomputable def observed (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (target : List Bool) (t : State (p.W + 1) (p.H + 1))
    (i : Fin l.portCount) : ℕ :=
  ((residual l p target t).filter fun q =>
    q.1.val = p.x i.val ∧ q.2.val = p.Y (AcceptanceProbe.level l hl i) + 2).card

/-- The actual surplus of boxes on the complete ordinary axis. -/
@[expose] def J (p : Scales.Parameters) {n : ℕ}
    (s t : State (p.W + 1) (p.H + 1)) (i : Fin n) : ℕ :=
  Inventory.count (ordinaryAxis p i.val) t - Inventory.count (ordinaryAxis p i.val) s

/-- The actual box deficit on the gate middle's truncated axis. -/
@[expose] def D (p : Scales.Parameters) {n : ℕ}
    (s t : State (p.W + 1) (p.H + 1)) (i : Fin n) : ℕ :=
  Inventory.count (gateAxis p i.val) s - Inventory.count (gateAxis p i.val) t

private theorem ordinary_lower_endpoint (l : PortLayout) (hl : l.pages.Valid) (i : Fin l.portCount)
    (hn : ¬ Partner.Middle l i.val) :
    ∃ lower ∈ l.endpoints, lower.side = .lower ∧ lower.port = i.val :=
  (l.endpoints_lower_or_gate hl i.isLt).resolve_right hn

private theorem middle_placement (l : PortLayout) {port : ℕ} (hm : Partner.Middle l port) :
    ∃ g ∈ placements l, ∃ kind, g.gate = some kind ∧ port = g.left + 1 := by
  obtain ⟨kind, first, hg, hport⟩ := hm
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
  let g : Placement := ⟨.lower, first, first + 2, l.lowerLevel i.val, l.lowerOffset i.val, some kind⟩
  have hzip : (LowerGroup.gate kind first, i.val) ∈ l.lowerGroups.zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    rw [List.getElem?_eq_getElem i.isLt]
    exact congrArg some hi
  refine ⟨g, ?_, kind, rfl, hport⟩
  apply List.mem_append_right
  apply List.mem_map.mpr
  exact ⟨(.gate kind first, i.val), hzip, by simp [encLowerGroup_elim, encLowerGroup_toSum, g]⟩

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- Every non-middle port satisfies the actual signed ordinary probe equation. -/
theorem canonical_ordinary {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (i : Fin l.portCount) (hn : ¬ Partner.Middle l i.val) :
    J p (I).initial t i + observed l p hl target t i = (target.getD i.val false).toNat := by
  obtain ⟨hu, hs, hp⟩ := AcceptanceProbe.upperEndpoint_spec l hl i
  obtain ⟨lower, hlow, hls, hlp⟩ := ordinary_lower_endpoint l hl i hn
  have h := canonical_ordinary_probe_balance_at_level l p hl hM haxes initial target hgate
    hu hlow hs hls (hlp.trans hp.symm) hr ha
  rw [hp] at h
  unfold J observed residual AcceptanceProbe.level
  convert h using 1

/-- Every actual gate middle satisfies the genuine target-plus-deficit probe inequality. -/
theorem canonical_middle {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (i : Fin l.portCount) (hm : Partner.Middle l i.val) :
    (target.getD i.val false).toNat + D p (I).initial t i ≤ observed l p hl target t i := by
  obtain ⟨hu, hs, hp⟩ := AcceptanceProbe.upperEndpoint_spec l hl i
  obtain ⟨g, hg, kind, hk, hmid⟩ := middle_placement l hm
  have h := canonical_gate_probe_deficit_at_level l p hl hM haxes initial target hgate
    hg hk hu hs (hp.trans hmid) hr ha
  rw [← hmid] at h
  unfold D observed residual AcceptanceProbe.level
  convert h using 1

/-- Every actual lower-WIRE port has zero ordinary-axis surplus. -/
theorem canonical_wire {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (i : Fin l.portCount) (hw : Partner.Ordinary l i.val) : J p (I).initial t i = 0 :=
  canonical_ordinary_wire_surplus_zero l p hl hM haxes initial target hgate hw hr .refl ha

/-- Every actual pre-probe residual on an original port column lies on that port's own allocated probe row. -/
theorem canonical_probe_port_location (i : Fin l.portCount) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ residual l p target t)
    (hrow : q.2.val ∈ probeRows l p) (hx : q.1.val = p.x i.val) :
    q.2.val = p.Y (AcceptanceProbe.level l hl i) + 2 := by
  classical
  obtain ⟨hu, hs, hp⟩ := AcceptanceProbe.upperEndpoint_spec l hl i
  have hstock : q ∈ probeColumnStock l p target (PushS.holes t) (AcceptanceProbe.upperEndpoint l hl i).port :=
    Finset.mem_filter.mpr ⟨hq, by simpa only [hp] using hx, hrow⟩
  by_cases hm : Partner.Middle l i.val
  · obtain ⟨g, hg, kind, hk, hmid⟩ := middle_placement l hm
    exact canonical_gate_probe_location l p hl hM haxes initial target hgate
      hg hk hu hs (hp.trans hmid) hr ha hstock
  · obtain ⟨lower, hlow, hls, hlp⟩ := ordinary_lower_endpoint l hl i hm
    exact canonical_ordinary_probe_location l p hl hM haxes initial target hgate
      hu hlow hs hls (hlp.trans hp.symm) hr ha hstock

end Canonical

end PushPuzzle.Push.AcceptanceProbeNumerics
