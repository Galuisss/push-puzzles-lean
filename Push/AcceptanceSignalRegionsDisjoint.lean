/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSignalRegionsCover
public import Push.AcceptanceSoundnessWirePaymentGeometry
import all PushS.PortWireGeometry
import all PushS.PortGateIndexing
import all PushS.PortSignalLocality
import all PushS.PortWalkBudget
import all Push.AcceptanceProgramLayout

/-! Actual accepted terminal stocks in the finite signal-region family are pairwise disjoint. -/

public section
namespace PushPuzzle.Push.AcceptanceSignalRegions

open PushFS PushS PushS.PortLayout AcceptanceProgram AcceptanceSoundness

private theorem axisRegion_gateRail_disjoint (l : PortLayout) (p : Scales.Parameters)
    (_hl : l.pages.Valid) (i : Fin l.portCount) {g : Placement}
    (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    Disjoint (axisRegion l p i) (gateOpenRail p g) := by
  apply Finset.disjoint_left.mpr
  intro q hi hr
  have hx := axisRegion_column l p i hi
  have hy := (Finset.mem_filter.mp hr).2
  have hd := p.outer_distance
  have hb := span_port_bounds p (r := 0) (by omega : 0 < p.D)
    (show p.x i.val - 0 ≤ q.1.val ∧ q.1.val ≤ p.x i.val + 0 by omega) hy.2.1 hy.2.2
  have hshape := placement_gate_shape l hg hk
  have hiL : i.val ≠ g.left := by intro h; rw [h] at hx; omega
  have hiR : i.val ≠ g.right := by intro h; rw [h] at hx; omega
  have hm : i.val = g.left + 1 := by omega
  have hc : i.val ∈ l.gateCenterCoordinates := hm ▸ center_of_gate l (placement_gate_mem l hg hk)
  simp only [axisRegion, hc, ite_true] at hi
  have hi := (Finset.mem_filter.mp hi).2
  omega

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- Actual accepted holes on an axis avoid every placement's open rail. -/
theorem canonical_axis_rail_disjoint {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (i : Fin l.portCount) {g : Placement} (hg : g ∈ placements l) :
    Disjoint (PushS.holes t ∩ axisRegion l p i) (railRegion p g) := by
  cases hk : g.gate with
  | none =>
    simp only [railRegion, hk]
    apply Finset.disjoint_left.mpr
    intro q haxis hrail
    obtain ⟨hq, hi⟩ := Finset.mem_inter.mp haxis
    have hx := axisRegion_column l p i hi
    apply canonical_wire_hole_not_axis l p hl hM haxes initial target hgate hg hk hr ha hq hrail
    change q.1.val ∈ ((List.range l.portCount).map p.x).toFinset
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, hx.symm⟩)
  | some kind =>
    simp only [railRegion, hk]
    exact (axisRegion_gateRail_disjoint l p hl i hg hk).mono Finset.inter_subset_right (fun _ h => h)

/-- Distinct indexed regions contain disjoint actual accepted terminal hole stocks. -/
theorem canonical_regions_pairwise {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Pairwise (fun i j : RegionIndex l =>
      Disjoint (PushS.holes t ∩ region l p i) (PushS.holes t ∩ region l p j)) := by
  classical
  intro i j hne
  rcases i with i | g <;> rcases j with j | h
  · exact (axisRegion_pairwise l p (fun h => hne (congrArg Sum.inl h))).mono
      Finset.inter_subset_right Finset.inter_subset_right
  · exact (canonical_axis_rail_disjoint l p hl hM haxes initial target hgate hr ha i
      (List.mem_toFinset.mp h.property)).mono (fun _ h => h) Finset.inter_subset_right
  · exact ((canonical_axis_rail_disjoint l p hl hM haxes initial target hgate hr ha j
      (List.mem_toFinset.mp g.property)).mono (fun _ h => h) Finset.inter_subset_right).symm
  · have hval : g.val ≠ h.val := fun he => hne (congrArg Sum.inr (Subtype.ext he))
    exact (railRegion_pairwise l p hl hM (List.mem_toFinset.mp g.property)
      (List.mem_toFinset.mp h.property) hval).mono Finset.inter_subset_right Finset.inter_subset_right

/-- The fixed stock and every indexed actual accepted terminal stock are pairwise disjoint. -/
theorem canonical_family_pairwise {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Pairwise (fun i j : Option (RegionIndex l) =>
      Disjoint (family l p (PushS.holes t) i) (family l p (PushS.holes t) j)) := by
  classical
  have hfixed (i : RegionIndex l) : Disjoint (fixedHoles l p) (PushS.holes t ∩ region l p i) := by
    rcases i with i | g
    · exact (fixedHoles_axisRegion_disjoint l p hl hM haxes i).mono (fun _ h => h) Finset.inter_subset_right
    · exact (fixedHoles_railRegion_disjoint l p hl hM haxes (List.mem_toFinset.mp g.property)).mono
        (fun _ h => h) Finset.inter_subset_right
  intro i j hne
  cases i with
  | none =>
    cases j with
    | none => exact (hne rfl).elim
    | some j => exact hfixed j
  | some i =>
    cases j with
    | none => exact (hfixed i).symm
    | some j =>
      exact canonical_regions_pairwise l p hl hM haxes initial target hgate hr ha
        (fun h => hne (congrArg some h))

end Canonical
end PushPuzzle.Push.AcceptanceSignalRegions
