/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateSampleTarget
public import Push.AcceptanceSoundnessGateExhausted
public import Push.AcceptanceSoundnessSupportHalf
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceProgramGateAxisReadStockPrefix
import all Push.AcceptanceProgramInterlevelStockWork
import all Push.AcceptanceProgramGuardStockReads
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramThirdClear
import all PushS.PortGatePrivateEntry
import all PushS.PortGateHalfRods
import all PushS.PortGatePageWindow
import all PushS.PortGatePublicWalk
import all PushS.PortCoreCrossing
import all PushS.PortSegments

/-! The actual R18 core payment certifies the zero sample after the open axis is exhausted. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

private theorem gate_zero_target_before_eighteen (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = p.x (g.left + 1))
    (hy : q.2.val = p.H - readDepth p 1) (htarget : q ∈ targetHoles l p target) :
    q ∈ (emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 18)
      (targetHoles l p target)).remaining := by
  have hi := center_of_gate l (placement_gate_mem l hg hk)
  have hcore : q.1.val ∈ cores l p := hx ▸ gate_core_column l p hi
  have hY := readDepth_add_lt_H p 1
  have hread := readDepth_eq p le_rfl p.levels_pos
  have hq15 := gate_axis_lower_band_before l p hl hM haxes target hg hk hx
    ⟨by rw [hread] at hy; omega, by rw [hread] at hy; omega⟩ htarget
  have htake : (schedule l p (targetHoles l p target \ Boundary.frame).card).take 18 =
      axisReadBefore l p target ++ [axisReadRound l p, .clear .north (axes l p \ cores l p),
        .clear .west (Finset.range (p.H + 1) \ thirdRowKeep l p)] := by
    simp only [axisReadBefore, schedule, preparation, frameSchedule, axisReadRound, thirdRowKeep]
    simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero]
  rw [htake, emit_remaining_append]
  apply emit_preserves _ _ hq15
  intro stage hs hregion
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · obtain ⟨⟨lane, span⟩, hreq, hcol, hdepth⟩ := (mem_readRegion _ _ q).mp hregion
    change q.1.val = lane at hcol
    rcases List.mem_append.mp hreq with hordinary | hcoreReq
    · have hn := ((mem_prefixRequests _ _ _ _).mp hordinary).1
      exact (Finset.mem_sdiff.mp hn).2 (hcol ▸ hcore)
    · have hn := ((mem_prefixRequests _ _ _ _).mp hcoreReq).2
      change q.2.val < span at hdepth
      rw [hn, hy, hread] at hdepth
      omega
  · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hregion).2).2 hcore
  · have hrow : q.2.val ∈ workRows l p := by
      apply List.mem_toFinset.mpr
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      exact ⟨readDepth p 1, by simpa only [Nat.zero_add] using (l.workingDepthCoordinates_mem p 0 p.levels_pos).1,
        by simpa only [List.mem_cons, List.not_mem_nil, or_false] using Or.inr hy⟩
    have hkeep : q.2.val ∈ thirdRowKeep l p := Finset.mem_union_left _ (Finset.mem_union_left _ hrow)
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hregion).2).2 hkeep

/-- Every canonical target zero sample is an actual terminal hole, using genuine R16 axis exhaustion. -/
theorem canonical_gate_zero_sample_terminal (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = p.x (g.left + 1))
    (hy : q.2.val = p.H - readDepth p 1) (htarget : q ∈ targetHoles l p target) : q ∈ holes t := by
  classical
  let T := targetHoles l p target
  let E := holes t
  let stages := schedule l p (T \ Boundary.frame).card
  let R := (emit (stages.take 18) T).remaining
  let A := roundResidual stages T E 18
  let F := roundResidual stages T E 19
  have hi := center_of_gate l (placement_gate_mem l hg hk)
  have hcore : q.1.val ∈ cores l p := hx ▸ gate_core_column l p hi
  have hY := readDepth_ge p le_rfl p.levels_pos
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have hdepth := readDepth_eq p le_rfl p.levels_pos
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) accepted).2
  have hindex : stages[18]? = some (.read .north (prefixRequests (cores l p) fun _ => p.H - p.Y 1 + 1)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have he := (roundResidual_step stages T E 18 hc hindex).1
  let marker : Cell (p.W + 1) (p.H + 1) := (q.1, ⟨p.H - p.Y 1 / 2, by rw [hdepth] at hY hD; omega⟩)
  have hm26 := canonical_core_half_marker_input l p hl hM haxes initial target hr accepted
    (q := marker) rfl hcore
  have hm19 := roundResidual_antitone stages T E hc (by omega : 19 ≤ 26) hm26
  have hexhaust := canonical_gate_axis_residual_sixteen_empty l p hl hM haxes initial target hgate
    hg hk hu hsu hp hr accepted
  have hstock : A.filter (fun a => Direction.north.lane a = q.1.val) \
      F.filter (fun a => Direction.north.lane a = q.1.val) ⊆ ({q} : Finset _) := by
    intro a ha
    obtain ⟨haA, haF⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨haA, hax⟩ := Finset.mem_filter.mp haA
    have hax : a.1.val = q.1.val := hax
    have haF' : a ∉ F := fun h => haF (Finset.mem_filter.mpr ⟨h, hax⟩)
    have hlt := round_deleted_before_retained .north _ _ he hm19 haA haF' hax.symm
    change a.2.val < p.H - p.Y 1 / 2 at hlt
    have haE := scan_subset (roundResidual_eval stages T E 18 hc) haA
    have hf := canonical_residual_not_frame l p hl hM haxes initial target hr accepted 18 (by omega) haA
    have ha0 : 0 < a.2.val := by
      by_contra hn
      exact hf ((Boundary.mem_frame a).mpr ⟨.north, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩)
    have hay : a.2.val = p.H - readDepth p 1 := by
      by_contra hn
      by_cases habove : a.2.val < p.H - readDepth p 1
      · have ha16 := roundResidual_antitone stages T E hc (by omega : 16 ≤ 18) haA
        apply Finset.notMem_empty a
        rw [← hexhaust]
        exact Finset.mem_inter.mpr ⟨ha16, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hax.trans hx, ha0, habove⟩⟩
      · have hrod : a ∈ l.gateHalfRods p := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, g.left + 1, hi, Or.inl (hax.trans hx), p.H - a.2.val, ?_, ?_, ?_⟩
          · rw [hdepth]
            omega
          · omega
          · have hb := a.2.isLt
            omega
        have hbox := avoiding_box
          (canonical_gate_private_avoiding_prefix l p hl hM haxes initial target hgate hi hr .refl accepted)
          (Finset.mem_union_right _ hrod)
          (l.gateHalfRods_initial_full p hl hM haxes (l.canonical initial) (l.canonical target) hrod)
        exact (mem_holes _).mp haE hbox
    exact Finset.mem_singleton.mpr (Prod.ext (Fin.ext hax) (Fin.ext (hay.trans hy.symm)))
  have hqR := gate_zero_target_before_eighteen l p hl hM haxes target hg hk hx hy htarget
  have hsub : ({q} : Finset _) ⊆ R.filter
      (fun a => Direction.north.lane a = q.1.val ∧ prefixRank .north a < p.H - p.Y 1 + 1) := by
    intro a ha
    cases Finset.mem_singleton.mp ha
    exact Finset.mem_filter.mpr ⟨hqR, rfl, by change q.2.val < p.H - p.Y 1 + 1; rw [hy, hdepth]; omega⟩
  have href := prefix_round_reference_card .north (cores l p) (fun _ => p.H - p.Y 1 + 1) R q.1.val hcore
  have hcard := Finset.card_le_card hsub
  have hpaid := round_lane_saturation .north (prefixRequests (cores l p) fun _ => p.H - p.Y 1 + 1)
    R A F {q} q.1.val he hstock (by omega)
  have hqPaid := (congrArg (fun S : Finset (Cell (p.W + 1) (p.H + 1)) => q ∈ S) hpaid).mp (Finset.mem_singleton_self q)
  exact scan_subset (roundResidual_eval stages T E 18 hc) (Finset.mem_filter.mp (Finset.mem_sdiff.mp hqPaid).1).1

end PushPuzzle.Push.AcceptanceSoundness
