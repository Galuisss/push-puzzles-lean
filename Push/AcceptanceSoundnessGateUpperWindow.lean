/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessGateProbeLedger
public import Push.AcceptanceGateFirstRod
public import Push.AcceptanceProbeWindow
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramTrimStock
import all PushS.PortGateAxisTrains
import all PushS.PortColumnRadius
import all PushS.PortEndpointCounts
import all PushS.PortSegments
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral

/-! Actual upper first-rod and deep-crossing inventories confine every gate R16 residue to its own working rows. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram

private theorem upper_third_bound (l : PortLayout) (p : Scales.Parameters) {y : ℕ}
    (hkeep : y ∈ thirdRowKeep l p) (hy : y ≤ p.D) : y ≤ p.Y p.levels + 2 ∨ y = p.D := by
  have hlast := last_depth_margin p
  have hD := readDepth_add_lt_D p p.levels
  rw [readDepth_eq p p.levels_pos le_rfl] at hD
  have h1 := readDepth_add_lt_D p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at h1
  have hH : p.H = 2 * p.D := rfl
  simp only [thirdRowKeep, Finset.mem_union, Finset.mem_singleton] at hkeep
  rcases hkeep with (hw | hc) | he
  · simp only [workRows, List.mem_toFinset, List.mem_append] at hw
    rcases hw with hb | hw
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      omega
    · obtain ⟨v, hv, hyv⟩ := List.mem_flatMap.mp hw
      have hm := workingRows_le_last l p hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hyv
      omega
  · simp only [cutRows, List.mem_toFinset, List.mem_append] at hc
    rcases hc with hb | hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      omega
    · obtain ⟨k, hk, hrow⟩ := List.mem_flatMap.mp hc
      have hk := List.mem_range.mp hk
      have hn := Y_le p (show k + 2 ≤ p.levels by omega)
      have hkn := Y_le p (show k + 1 ≤ k + 2 by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      omega
  · omega

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) {g : Placement} (hg : g ∈ placements l)
  {kind : Shuttle.Kind} (hk : g.gate = some kind)
  {upper : Endpoint} (hu : upper ∈ l.endpoints) (hupper : upper.side = .upper) (hport : upper.port = g.left + 1)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hg hk hu hupper hport

private theorem gate_upper_middle_initial_full {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x (g.left + 1)) (hlo : readDepth p upper.level + 2 < q.2.val)
    (hhi : q.2.val ≤ p.D) : q ∈ (I).initial.boxes := by
  have holes : PushS.holes ((I).initial : State (p.W + 1) (p.H + 1)) = targetHoles l p initial :=
    canonical_initial_holes l p hl hM haxes initial target
  have raw := l.encodedSegments_gateAxis_train_boxes p hl hM haxes (l.canonical initial)
    hg hk hu hupper hport (I).initial holes q
  have hD := readDepth_add_lt_D p upper.level
  have h1 := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have hb := Bool.toNat_le ((l.canonical initial).axes.getD upper.port false)
  apply Finset.mem_inter.mp ((raw).mpr ⟨hx, ?_⟩) |>.1
  rw [TwoBlocks.mem_slots]
  simp only [gateAxisTrainBlocks]
  right
  constructor <;> omega

include hgate

/-- Before any deficit cancellation, every real R16 gate-axis residue lies on its own upper work or probe row. -/
theorem canonical_gate_residual_sixteen_own_rows
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 16 ∩ gateAxis p (g.left + 1)) :
    q.2.val = p.Y upper.level ∨ q.2.val = p.Y upper.level + 2 := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hq16 := (Finset.mem_inter.mp hq).1
  have hqE := scan_subset (roundResidual_eval stages T E 16 hc) hq16
  obtain ⟨_, hx, hy0, _⟩ := Finset.mem_filter.mp (Finset.mem_inter.mp hq).2
  have hhi := canonical_gate_no_lower_residual_sixteen l p hl hM haxes initial target hg hk hgate hr ha hq
  have i16 : stages[16]? = some (.clear .north (axes l p \ cores l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have i17 : stages[17]? = some (.clear .west (Finset.range (p.H + 1) \ thirdRowKeep l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, thirdRowKeep, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq17 := (roundResidual_clear_keeps stages T E 16 hc i16 hq16).1
  have hn := (roundResidual_clear_keeps stages T E 17 hc i17 hq17).2
  change q.2.val ∉ Finset.range (p.H + 1) \ thirdRowKeep l p at hn
  have hkeep : q.2.val ∈ thirdRowKeep l p := by
    by_contra hnot
    exact hn (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr q.2.isLt, hnot⟩)
  have hDne : q.2.val ≠ p.D := by
    intro heq
    exact (PushS.mem_holes _).mp hqE
      (canonical_main_central_occupied l p hl hM haxes initial target
        (gate_middle_lt l hl (placement_gate_mem l hg hk)) hx (by omega) hr .refl ha)
  have hmax : q.2.val ≤ p.Y p.levels + 2 := (upper_third_bound l p hkeep hhi).resolve_right hDne
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM hu
  have hlo : p.Y upper.level ≤ q.2.val := by
    by_contra hnot
    exact (PushS.mem_holes _).mp hqE
      (canonical_gate_upper_first_rod_full l p hl hM haxes initial target hgate hg hk hu hupper hport hr ha
        hx (by omega) (by rw [readDepth_eq p hj hjm]; omega))
  apply upper_third_window l p hj hjm hkeep hlo
  by_contra hnlt
  have hge : trimDepth p upper.level ≤ q.2.val := by omega
  by_cases hlast : upper.level = p.levels
  · have hlastD := readDepth_add_lt_D p p.levels
    rw [readDepth_eq p p.levels_pos le_rfl] at hlastD
    rw [trimDepth, ite_eq_right (by omega)] at hge
    have hmax' := hmax
    rw [← hlast] at hmax'
    omega
  · have heM : upper.level < p.levels := by omega
    have htrim := trimDepth_gt_work p hj hjm
    have hband : q ∈ axisDeepBand p upper.side upper.port upper.level := by
      refine ⟨?_, ?_⟩
      · rw [hport, hx, Nat.dist_self]
        omega
      · simp only [hupper, ite_true]
        rw [readDepth_eq p hj hjm, readDepth_eq p (by omega) (by omega)]
        rw [trimDepth, ite_eq_left heM] at hge
        exact ⟨hge, hmax⟩
    have hinit := gate_upper_middle_initial_full l p hl hM haxes initial target hg hk hu hupper hport hx
      (by rw [readDepth_eq p hj hjm]; omega) hhi
    exact (PushS.mem_holes _).mp hqE
      (canonical_endpoint_deep_occupied l p hl hM haxes initial target hgate upper hu heM hband hinit hr .refl ha)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
