/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateSamplesPrivate
public import Push.AcceptanceGateSamplesReference
public import Push.AcceptanceSoundnessWideSaturation
import all Push.AcceptanceSoundnessSupportMarkerResidual
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceProgramLayout
import all PushS.PortGatePrivateWalk
import all PushS.PortSegments

/-! The actual lower sample read certifies every canonical work-row hole at offsets two and ten. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- Physical payment slots on one independent short-train sample column. -/
@[expose] def gateSampleSlots (p : Scales.Parameters) (middle x : ℕ) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  Finset.univ.filter fun q => q.1.val = x ∧
    (q.2.val = p.H - readDepth p 1 ∨ (x = p.x middle + 2 ∧ q.2.val = p.H - (readDepth p 1 + 2)))

/-- Every canonical target hole at either independent sample is an actual accepted terminal hole. -/
theorem canonical_gate_independent_sample_terminal (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x middle + 2 ∨ q.1.val = p.x middle + 10)
    (hy : q.2.val = p.H - readDepth p 1) (htarget : q ∈ targetHoles l p target) : q ∈ holes t := by
  classical
  let T := targetHoles l p target
  let E := holes t
  let stages := schedule l p (T \ Boundary.frame).card
  let R := (emit (stages.take 21) T).remaining
  let A := roundResidual stages T E 21
  let F := roundResidual stages T E 22
  let S := gateSampleSlots p middle q.1.val
  have hxsample : q.1.val ∈ samples l p := by
    apply List.mem_toFinset.mpr
    apply List.mem_flatMap.mpr
    exact ⟨middle, hi, by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hx⟩
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) accepted).2
  have hindex : stages[21]? = some (.read .south (prefixRequests (samples l p) fun _ => p.D - 4)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have he := (roundResidual_step stages T E 21 hc hindex).1
  obtain ⟨marker, hmx, hmy, hm⟩ := actual_sample_marker l p q.1 hxsample
  have hm22 := sample_markers_residual l p hl hM haxes initial target hr
    (canonical_initial_frame l p hl hM haxes initial target)
    (canonical_initial_holes l p hl hM haxes initial target) accepted (newCentralMarkers_subset l p hm) hmy
  have hstock : A.filter (fun a => Direction.south.lane a = q.1.val) \
      F.filter (fun a => Direction.south.lane a = q.1.val) ⊆ S := by
    intro a ha
    obtain ⟨haA, haF⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨haA, hax⟩ := Finset.mem_filter.mp haA
    have hax : a.1.val = q.1.val := hax
    have haF' : a ∉ F := fun h => haF (Finset.mem_filter.mpr ⟨h, hax⟩)
    have hlt := round_deleted_before_retained .south _ _ he hm22 haA haF'
      ((congrArg Fin.val hmx).trans hax.symm)
    have hf := canonical_residual_not_frame l p hl hM haxes initial target hr accepted 21 (by omega) haA
    have haE := scan_subset (roundResidual_eval stages T E 21 hc) haA
    have hloc := canonical_gate_sample_lower_location l p hl hM haxes initial target hgate hr accepted hi
      (q := a) (by rw [hax]; exact hx) (by simp only [prefixRank, Nat.add_sub_cancel, hmy] at hlt; omega) hf haE
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hax, ?_⟩
    exact hloc.imp id (fun h => ⟨hax ▸ h.1, h.2⟩)
  have hY := readDepth_ge p le_rfl p.levels_pos
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have hreference : S ⊆ R.filter (fun a => Direction.south.lane a = q.1.val ∧ prefixRank .south a < p.D - 4) := by
    intro a ha
    obtain ⟨_, hax, haloc⟩ := Finset.mem_filter.mp ha
    have hatarget : a ∈ targetHoles l p target := by
      rcases haloc with hawork | ⟨htwo, habranch⟩
      · have haq : a = q := Prod.ext (Fin.ext hax) (Fin.ext (hawork.trans hy.symm))
        exact haq.symm ▸ htarget
      · apply l.gatePrivateWalk_subset_encoded p (l.canonical target) hi
        apply (mem_gatePrivateWalk p middle).mpr
        right
        right
        exact ⟨habranch, by omega, by omega⟩
    have hay : a.2.val = p.H - readDepth p 1 ∨ a.2.val = p.H - (readDepth p 1 + 2) :=
      haloc.imp id And.right
    have haR := sample_target_before_twenty_one l p hl hM haxes target (hax ▸ hxsample) hay hatarget
    exact Finset.mem_filter.mpr ⟨haR, hax, by change p.H + 1 - 1 - a.2.val < p.D - 4; omega⟩
  have href := prefix_round_reference_card .south (samples l p) (fun _ => p.D - 4) R q.1.val hxsample
  have hcard := Finset.card_le_card hreference
  have hpaid := round_lane_saturation .south (prefixRequests (samples l p) fun _ => p.D - 4) R A F S q.1.val
    he hstock (by omega)
  have hqS : q ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, Or.inl hy⟩
  rw [hpaid] at hqS
  exact scan_subset (roundResidual_eval stages T E 21 hc) (Finset.mem_filter.mp (Finset.mem_sdiff.mp hqS).1).1

end PushPuzzle.Push.AcceptanceSoundness
