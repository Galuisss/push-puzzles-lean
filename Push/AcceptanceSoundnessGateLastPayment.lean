/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateLowerPrefix
public import Push.AcceptanceSoundnessGateLast
public import Push.AcceptanceSoundnessMainResidual
import all Push.AcceptanceProgramMainStockGeometry
import all Push.AcceptanceSoundnessSupportLanes
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all PushS.PortGateIndexing
import all PushS.PortGatePageWindow
import all PushS.PortCoreCrossing
import all PushS.PortSegments

/-! The last lower gap hole, when present, certifies exhaustion of the actual open gate axis at R16. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hg hk

/-- A real terminal nearest-work hole and actual north-read ordering force the complete R16 gate-axis stock empty. -/
private theorem canonical_gate_axis_exhausted_of_last_hole
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {last : Cell (p.W + 1) (p.H + 1)} (hlastX : last.1.val = p.x (g.left + 1))
    (hlastY : last.2.val = p.H - (p.Y 1 + 1)) (hlast : last ∈ PushS.holes t) :
    roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 16 ∩ gateAxis p (g.left + 1) = ∅ := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have gate := placement_gate_mem l hg hk
  have hp := gate_middle_lt l hl gate
  have hYH := readDepth_add_lt_H p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hYH
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  obtain ⟨hq16, hqaxis⟩ := Finset.mem_inter.mp hq
  obtain ⟨_, hqx, _, hqy⟩ := Finset.mem_filter.mp hqaxis
  have horder : q.2.val ≤ last.2.val := by
    rw [readDepth_eq p le_rfl p.levels_pos] at hqy
    omega
  have hlast6 : last ∈ roundResidual stages T E 6 := by
    have he := canonical_main_input_axis l p hl hM haxes initial target hp hr ha
    have hm : last ∈ E ∩ ordinaryAxis p (g.left + 1) :=
      Finset.mem_inter.mpr ⟨hlast, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlastX, by omega, by omega⟩⟩
    have hm' := (congrArg (fun S : Finset (Cell (p.W + 1) (p.H + 1)) => last ∈ S) he).mpr hm
    exact (Finset.mem_filter.mp hm').1
  have i6 : stages[6]? = some (mainTop l p) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq7 := roundResidual_antitone stages T E hc (show 7 ≤ 16 by omega) hq16
  have hlast7 : last ∈ roundResidual stages T E 7 := by
    by_contra hn
    have hlt := round_deleted_before_retained .north _ _ (roundResidual_step stages T E 6 hc i6).1
      hq7 hlast6 hn (hqx.trans hlastX.symm)
    change last.2.val < q.2.val at hlt
    omega
  have i7 : stages[7]? = some (mainBottom l p) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hlast8 := roundResidual_unread_keeps stages T E 7 hc i7 hlast7 (by
    intro ht
    obtain ⟨request, hrequest, hcol⟩ := ht
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hrequest
    obtain ⟨he, hs⟩ := List.mem_filter.mp he
    have hs : e.side = .lower := of_decide_eq_true hs
    have hx : p.x e.port = p.x (g.left + 1) := by
      change last.1.val = request.1 at hcol
      have hm := congrArg Prod.fst heq
      omega
    have hep := axis_injective p hx
    exact l.endpoints_lower_ne_gate_middle hl gate he hs hep)
  have hstock := canonical_main_to_probe_stock l p hl hM haxes initial target hp hr ha
  have hlast13 : last ∈ roundResidual stages T E 13 := by
    have hm' := (congrArg (fun S : Finset (Cell (p.W + 1) (p.H + 1)) => last ∈ S) hstock).mpr
      (Finset.mem_filter.mpr ⟨hlast8, hlastX⟩)
    exact (Finset.mem_filter.mp hm').1
  have hnProbe : last.2.val ∉ probeRows l p := by
    intro hy
    obtain ⟨e, he, hy⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
    obtain ⟨he, _⟩ := List.mem_filter.mp he
    obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
    have hD := readDepth_add_lt_D p e.level
    rw [readDepth_eq p hj hjm] at hD
    have h1 := readDepth_add_lt_D p 1
    rw [readDepth_eq p le_rfl p.levels_pos] at h1
    have hH : p.H = 2 * p.D := rfl
    change p.Y e.level + 2 = last.2.val at hy
    omega
  have i13 : stages[13]? = some (readRows p .west (probeRows l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hlast14 := roundResidual_unread_keeps stages T E 13 hc i13 hlast13
    (fun ht => hnProbe (row_touches p .west _ (Or.inl rfl) ht))
  have i14 : stages[14]? = some (.clear .east (probeRows l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hlast15 := (roundResidual_clear_keeps stages T E 14 hc i14 hlast14).1
  have i15 : stages[15]? = some (axisReadRound l p) := by
    simp only [stages, schedule, preparation, frameSchedule, axisReadRound, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hlast16 : last ∈ roundResidual stages T E 16 := by
    by_contra hn
    have hlt := round_deleted_before_retained .north _ _ (roundResidual_step stages T E 15 hc i15).1
      hq16 hlast15 hn (hqx.trans hlastX.symm)
    change last.2.val < q.2.val at hlt
    omega
  exact canonical_gate_last_not_residual_sixteen l p hl hM haxes initial target hr ha hlastY hlast16

/-- The actual R16 gate-axis residue has no lower-half hole, before any gate deficit is cancelled. -/
theorem canonical_gate_no_lower_residual_sixteen (hgate : l.gateCenterCoordinates ≠ [])
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 16 ∩ gateAxis p (g.left + 1)) : q.2.val ≤ p.D := by
  by_contra hn
  have hqlo : p.D < q.2.val := by omega
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hqE := scan_subset (roundResidual_eval _ _ _ 16 hc) (Finset.mem_inter.mp hq).1
  have hx := (Finset.mem_filter.mp (Finset.mem_inter.mp hq).2).2.1
  have hYH := readDepth_add_lt_H p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hYH
  let last : Cell (p.W + 1) (p.H + 1) := (q.1, ⟨p.H - (p.Y 1 + 1), by omega⟩)
  have hlast := canonical_gate_lower_hole_near_work l p hl hM haxes initial target hgate hg hk hr ha
    (Finset.mem_inter.mpr ⟨hqE, (Finset.mem_inter.mp hq).2⟩) hqlo
    (r := last) hx (by change p.H - (p.Y 1 + 1) + 1 = p.H - readDepth p 1; rw [readDepth_eq p le_rfl p.levels_pos]; omega)
  have hempty := canonical_gate_axis_exhausted_of_last_hole l p hl hM haxes initial target hg hk hr ha
    (last := last) hx rfl hlast
  exact Finset.notMem_empty q (hempty ▸ hq)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
