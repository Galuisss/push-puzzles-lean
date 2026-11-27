/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessPageFirst
public import Push.AcceptanceProgramPageRowLocation
import all Push.AcceptanceSoundnessSupportInterlevel
import all Push.AcceptanceSoundnessSupportCutResidual
import all Push.AcceptanceSoundnessCentralSamples
import all Push.AcceptanceSoundnessSupportLanes
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgram

/-! Actual late marker payments certify the second sparse support on the two separate physical pages. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

-- Classify every late read block and its exact marker-payment prefix in one proof.
set_option maxHeartbeats 600000 in
/-- The accepted terminal stock, with central markers filled, lies on the second separate-page sparse support. -/
theorem canonical_terminal_page_second_supported (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Support.Supported (twoPageSecond l p hl).support (Blocked.fill t (l.centralMarkers p)) := by
  intro q hq
  have hqE : q ∈ PushS.holes t := (PushS.mem_holes _).mpr (fun hb => hq (Finset.mem_union_left _ hb))
  have hcentral : q ∉ l.centralMarkers p := fun hm => hq (Finset.mem_union_right _ hm)
  by_contra hout
  have hwork : q.2.val ∉ workRows l p := fun hy => hout (Or.inl ((working_rows_iff l p q.2).mp hy))
  have hvert : q ∉ (l.twoPageStreets p hl).vertical := by
    intro hv
    apply hout
    right
    rcases hv with hm | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl hm
    · exact Or.inr (Or.inl ⟨Or.inl (Or.inl hx), hy⟩)
    · exact Or.inr (Or.inr ⟨Or.inl (Or.inl hx), hy⟩)
  have hadded : q.1.val ∉ guards l p ∪ samples l p := by
    intro hx
    have htop : q.1 ∈ (twoPageSecond l p hl).top := by
      rcases Finset.mem_union.mp hx with hg | hs
      · exact Or.inl (Or.inr hg)
      · exact Or.inr hs
    have hbottom : q.1 ∈ (twoPageSecond l p hl).bottom := by
      rcases Finset.mem_union.mp hx with hg | hs
      · exact Or.inl (Or.inr hg)
      · exact Or.inr hs
    rcases le_total q.2.val p.D with hy | hy
    · exact hout (Or.inr (Or.inr (Or.inl ⟨htop, hy⟩)))
    · exact hout (Or.inr (Or.inr (Or.inr ⟨hbottom, hy⟩)))
  have hguard : q.1.val ∉ guards l p := fun hx => hadded (Finset.mem_union_left _ hx)
  have hsample : q.1.val ∉ samples l p := fun hx => hadded (Finset.mem_union_right _ hx)
  have haxis : q.1.val ∉ axes l p := by
    intro hx
    obtain ⟨i, hi, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact hvert (Or.inl ((l.mainColumnSet_iff p q.1).mpr (Or.inr (Or.inr ⟨i, List.mem_range.mp hi, he.symm⟩))))
  have hq18 := canonical_off_page_residual_eighteen l p hl hM haxes initial target hr ha hqE hcentral hwork hvert
  have hframe := canonical_residual_not_frame l p hl hM haxes initial target hr ha 18 (by omega) hq18
  have hnewRows : q.2.val ∉ newMarkerRows p := by
    intro hy
    exact hcentral (newCentralMarkers_subset l p (program_new_rows_stock l p hl hM haxes initial target hr
      (canonical_initial_frame l p hl hM haxes initial target)
      (canonical_initial_holes l p hl hM haxes initial target) ha hqE hframe hy))
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have i18 : stages[18]? = some (.read .north (prefixRequests (cores l p) fun _ => p.H - p.Y 1 + 1)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq19 := roundResidual_unread_keeps stages T E 18 hc i18 hq18
    (fun ht => haxis (l.acceptanceCore_subset_axes p hl (prefix_touches p .north _ _ ht)))
  have i19 : stages[19]? = some (readColumns p .south (guards l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq20 := roundResidual_unread_keeps stages T E 19 hc i19 hq19 (fun ht => hguard (prefix_touches p .south _ _ ht))
  have i20 : stages[20]? = some (.clear .north (guards l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq21 := (roundResidual_clear_keeps stages T E 20 hc i20 hq20).1
  have i21 : stages[21]? = some (.read .south (prefixRequests (samples l p) fun _ => p.D - 4)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq22 := roundResidual_unread_keeps stages T E 21 hc i21 hq21 (fun ht => hsample (prefix_touches p .south _ _ ht))
  have i22 : stages[22]? = some (readRows p .east {p.D + 4}) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq23 := roundResidual_unread_keeps stages T E 22 hc i22 hq22 (by
    intro ht
    have hh := Finset.mem_singleton.mp (row_touches p .east _ (Or.inr rfl) ht)
    exact hnewRows (by simp [newMarkerRows, hh]))
  have i23 : stages[23]? = some (readRows p .west (workRows l p \ ({0, p.H} ∪ probeRows l p))) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq24 := roundResidual_unread_keeps stages T E 23 hc i23 hq23
    (fun ht => hwork (Finset.mem_sdiff.mp (row_touches p .west _ (Or.inl rfl) ht)).1)
  have i24 : stages[24]? = some (.clear .north (Finset.range (p.W + 1) \ (auxiliaries l p ∪ cores l p))) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq25 := (roundResidual_clear_keeps stages T E 24 hc i24 hq24).1
  have he := canonical_page_check_execution l p hl hM haxes initial target hr ha
  obtain ⟨pay⟩ := round_payment (pageCheckStages l p) (pageCheckTarget l p target) _ he.1 he.2 hq25
  rcases page_read_location l p pay.before pay.after pay.side pay.requests q pay.split pay.on_line with
      hsouth | ⟨hy, hbefore⟩ | ⟨side, j, hj, hjm, hy, hbefore⟩
  · have hy := canonical_page_south_payment_cut l p hl hM haxes initial target hr ha pay hsouth
    have haux : q.1.val ∈ auxiliaries l p :=
      (Finset.mem_union.mp (canonical_page_residual_columns l p hl hM haxes initial target hr ha hq25)).resolve_right
        (fun hx => haxis (l.acceptanceCore_subset_axes p hl hx))
    exact hcentral (auxiliary_central_marker l p haux hy)
  · have hlen : pay.before.length = 1 := by rw [hbefore, halfPrefix_length]
    have hqp := (congrArg (fun A : Finset (Cell (p.W + 1) (p.H + 1)) => q ∈ A) pay.input_roundResidual).mp pay.present
    simp only [hlen] at hqp
    have hq26 : q ∈ roundResidual stages T E (25 + 1) := by
      rw [canonical_pageResidual_eq l p hl hM haxes initial target hr ha]
      exact hqp
    exact haxis (l.acceptanceCore_subset_axes p hl
      (canonical_half_input_core_stock l p hl hM haxes initial target hr ha hq26 hy))
  · have hlen : pay.before.length = interlevelIndex l p side j := by
      rw [hbefore, interlevelPrefix_length l p side hj hjm]
    have hqp := (congrArg (fun A : Finset (Cell (p.W + 1) (p.H + 1)) => q ∈ A) pay.input_roundResidual).mp pay.present
    simp only [hlen] at hqp
    obtain ⟨a, hac, _, hcol⟩ := interlevel_actual_metadata l p hl hM haxes initial target hr ha side hj hjm hqp hy
    have hpage : q.1 ∈ l.pageColumnSet p side := by
      change q.1.val ∈ l.pageColumnCoordinates p side
      rw [hcol]
      exact acceptance_column_page l p side hac
    have hb := interlevelDepth_bounds p hj hjm
    have hH : p.H = 2 * p.D := rfl
    apply hout
    right
    cases side with
    | upper =>
      refine Or.inr (Or.inl ⟨Or.inl (Or.inl hpage), ?_⟩)
      change q.2.val ≤ p.D
      simp only [interlevelRow, ite_true] at hy
      omega
    | lower =>
      refine Or.inr (Or.inr ⟨Or.inl (Or.inl hpage), ?_⟩)
      change p.D ≤ q.2.val
      simp only [interlevelRow, reduceCtorEq, ite_false] at hy
      omega

end PushPuzzle.Push.AcceptanceSoundness
