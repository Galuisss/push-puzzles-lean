/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessProbeOrdinary
public import Push.AcceptanceFirstRod
import all PushS.PortUpperAxisNoInput
import all PushS.PortStreetSeparation
import all PushS.PortSegments
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral

/-! The actual ordinary-column probe observation belongs to its own upper working level. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) {upper lower : Endpoint}
  (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
  (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hu hlow hsuSide hslSide hport

/-- Every actually paid ordinary-column probe is on the genuine upper endpoint's own level. -/
theorem canonical_ordinary_probe_location {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ probeColumnStock l p target (PushS.holes t) upper.port) :
    q.2.val = p.Y upper.level + 2 := by
  obtain ⟨hq, hx, hrows⟩ := Finset.mem_filter.mp hq
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hqE := scan_subset (roundResidual_eval _ _ _ 13 hc) hq
  obtain ⟨e, he, hy⟩ := List.mem_map.mp (List.mem_toFinset.mp hrows)
  obtain ⟨he, _⟩ := List.mem_filter.mp he
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM hu
  obtain ⟨hk, hkm⟩ := l.endpoints_level_bounds p hl hM he
  change p.Y e.level + 2 = q.2.val at hy
  have hYk := readDepth_ge p hk hkm
  rw [readDepth_eq p hk hkm] at hYk
  rcases lt_trichotomy e.level upper.level with hlt | heq | hlt
  · have hgap := depth_gap p hk hlt hjm
    rw [readDepth_eq p hk hkm, readDepth_eq p hj hjm] at hgap
    have hfull := canonical_upper_first_rod_full l p hl hM haxes initial target hgate
      hu hlow hsuSide hslSide hport hr ha hx (by omega)
      (by rw [readDepth_eq p hj hjm]; omega)
    exact ((PushS.mem_holes _).mp hqE hfull).elim
  · simpa only [heq] using hy.symm
  · have heM : upper.level < p.levels := by omega
    have hgap := depth_gap p hj hlt hkm
    have hnext := next_depth_le p hj hlt hkm
    have hmax := Y_le p hkm
    have hv : readDepth p e.level + 2 ∈ l.workingDepthCoordinates p := by
      have hv := (l.workingDepthCoordinates_mem p (e.level - 1) (by omega)).2
      simpa only [Nat.sub_add_cancel hk] using hv
    have hband : q ∈ axisDeepBand p upper.side upper.port upper.level := by
      refine ⟨?_, ?_⟩
      · rw [hx, Nat.dist_self]
        omega
      · simp only [hsuSide, ite_true]
        rw [readDepth_eq p hk hkm] at hnext
        rw [readDepth_eq p hk hkm] at hgap
        omega
    have hfull := endpoint_axis_deep_initial_full l p hl hM haxes (l.canonical initial) (l.canonical target)
      upper hu hv (by rw [readDepth_eq p hk hkm, readDepth_eq p hj hjm] at hgap ⊢; omega) hx
      (by simpa only [hsuSide, ite_true, readDepth_eq p hk hkm] using hy.symm)
    exact ((PushS.mem_holes _).mp hqE
      (canonical_endpoint_deep_occupied l p hl hM haxes initial target hgate upper hu heM hband hfull hr .refl ha)).elim

/-- The ordinary column's entire paid probe stock is exactly its own upper-level point stock. -/
private theorem canonical_ordinary_probe_stock {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    probeColumnStock l p target (PushS.holes t) upper.port =
      (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 13).filter
          fun q => q.1.val = p.x upper.port ∧ q.2.val = p.Y upper.level + 2 := by
  ext q
  constructor
  · intro hq
    have hy := canonical_ordinary_probe_location l p hl hM haxes initial target hgate hu hlow
      hsuSide hslSide hport hr ha hq
    obtain ⟨hq, hx, _⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hq, hx, hy⟩
  · intro hq
    obtain ⟨hq, hx, hy⟩ := Finset.mem_filter.mp hq
    have hrow : p.Y upper.level + 2 ∈ probeRows l p := by
      apply List.mem_toFinset.mpr
      apply List.mem_map.mpr
      exact ⟨upper, List.mem_filter.mpr ⟨hu, by simp only [hsuSide, beq_self_eq_true]⟩, rfl⟩
    exact Finset.mem_filter.mpr ⟨hq, hx, hy ▸ hrow⟩

/-- The true signed ordinary probe balance is located on its own upper reading level. -/
theorem canonical_ordinary_probe_balance_at_level {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    (Inventory.count (ordinaryAxis p upper.port) t - Inventory.count (ordinaryAxis p upper.port) (I).initial) +
      ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 13).filter
          fun q => q.1.val = p.x upper.port ∧ q.2.val = p.Y upper.level + 2).card =
      (target.getD upper.port false).toNat := by
  have h := canonical_ordinary_probe_balance l p hl hM haxes initial target hgate hu hlow hsuSide hslSide hport hr ha
  rwa [canonical_ordinary_probe_stock l p hl hM haxes initial target hgate hu hlow hsuSide hslSide hport hr ha] at h

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
