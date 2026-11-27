/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasVector
public import PushPush.Doors.QuotasProbe
public import PushPush.Doors.QuotasAgreement
public import PushPush.Doors.QuotasFrameReadout
public import PushPush.WholeParallel

/-! The actual fourth whole-run round restores the original rack and all marker boxes. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction)
open Push.AcceptanceProgram
open WholeScan

def frameRounds (I : Instance) : List Round :=
  (Push.AcceptanceProgram.emit ((layout false I).quotaTemplates.take 3)
    (layout false I).referenceHoles).rounds

def frameCells (I : Instance) : Finset (Cell (layout false I).width (layout false I).height) :=
  Finset.univ.filter fun p => p.1.val = 0 ∨ p.1.val + 1 = (layout false I).width ∨
    p.2.val = 0 ∨ p.2.val + 1 = (layout false I).height

theorem frameRounds_remaining (I : Instance)
    (E : Finset (Cell (layout false I).width (layout false I).height))
    (hframe : ∀ p, Boundary p → p ∈ E) :
    Push.Scan.eval (instructions (frameRounds I)) E = some (E \ frameCells I) := by
  have heq : (Push.AcceptanceProgram.emit ((layout false I).quotaTemplates.take 3) E).rounds =
      frameRounds I := emit_rounds_agree _ _ _ (by
    intro p hp
    have hb := (frame_region I p).mp hp
    exact iff_of_true (hframe p hb) (reference_boundary I p hb))
  have he := emit_eval ((layout false I).quotaTemplates.take 3) E
  rw [heq, emit_remaining] at he
  have hregion : allRegions (w := (layout false I).width) (h := (layout false I).height)
      ((layout false I).quotaTemplates.take 3) = frameCells I := by
    ext p
    simpa only [frameCells, Finset.mem_filter, Finset.mem_univ, true_and, Boundary] using frame_region I p
  rwa [hregion] at he

structure ProbeWitness (I : Instance)
    (E : Finset (Cell (layout false I).width (layout false I).height)) where
  after : Finset (Cell (layout false I).width (layout false I).height)
  run : Exec (Push.Scan.lines .east (probeQuotas I)) (E \ frameCells I) after

private theorem ProbeWitness.before_interior {I : Instance}
    {E : Finset (Cell (layout false I).width (layout false I).height)} (_W : ProbeWitness I E)
    {p : Cell (layout false I).width (layout false I).height}
    (hp : p ∈ E \ frameCells I) : ¬ Boundary p := by
  intro hb
  exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)

theorem ProbeWitness.rack_box {I : Instance}
    {final : PushFS.State (layout false I).width (layout false I).height}
    (W : ProbeWitness I final.boxesᶜ)
    (hsupport : Supported .east (layout false I).rackX final)
    {row : ℕ} (hrow : row ∈ (layout false I).rackProbeRows)
    (p : Cell (layout false I).width (layout false I).height)
    (hx : p.1.val = (layout false I).rackX) (hy : p.2.val = row) : p ∈ final.boxes := by
  have hread := W.run.parallel_read .east (probeQuotas I) row
  rw [rackProbe_quotaAt I hrow] at hread
  have hfit := (layout_fits false I).rack_interior (rackProbe_rack I hrow)
  have hP := (layout false I).rackX_ge
  have hnot := rack_probe_blocked I hread.eval hread.no_split (by
      intro q hq hborder hmem
      have hbefore := (Finset.mem_filter.mp hmem).1
      exact W.before_interior hbefore (Or.inr (Or.inl hborder))) (by
      intro q hq hqx hborder
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr ?_, ?_⟩, hq⟩
      · intro hb
        have hs := hsupport q hb
        change (q.1.val : ℤ) ≤ (layout false I).rackX at hs
        omega
      · intro hb
        have hb := (Finset.mem_filter.mp hb).2
        dsimp at hfit
        omega) p hy hx
  by_contra hp
  apply hnot
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hp, ?_⟩, hy⟩
  intro hb
  have hb := (Finset.mem_filter.mp hb).2
  dsimp at hfit
  unfold Layout.width at hb
  omega

theorem ProbeWitness.rack_eq {I : Instance}
    {final : PushFS.State (layout false I).width (layout false I).height}
    (W : ProbeWitness I final.boxesᶜ)
    (hactual : Reachable (puzzle false I).initial final) (hinterior : Interior final) :
    line .south (layout false I).rackX final.boxes =
      line .south (layout false I).rackX (puzzle false I).initial.boxes := by
  have hsupport := hactual.supported hinterior (initial_supported false I)
  have hsub : line .south (layout false I).rackX (puzzle false I).initial.boxes ⊆
      line .south (layout false I).rackX final.boxes := by
    intro z hz
    obtain ⟨p, hp, hx, he⟩ := mem_line.mp hz
    have hp := ((layout false I).mem_raster _ _).mp hp
    change p.1.val = (layout false I).rackX at hx
    rw [hx, (layout false I).initialRaw_rack_iff] at hp
    have hm : (p.1.val, p.2.val) ∈ (layout false I).rack := by simpa only [hx] using hp
    change (p.1.val, p.2.val) ∈ (layout false I).rackList.toFinset at hm
    have hr : p.2.val ∈ (layout false I).rackProbeRows :=
      List.mem_map.mpr ⟨(p.1.val, p.2.val), List.mem_toFinset.mp hm, rfl⟩
    exact mem_line.mpr ⟨p, W.rack_box hsupport hr p hx rfl, hx, he⟩
  exact (Finset.eq_of_subset_of_card_le hsub
    (hactual.rack_card_le (initial_supported false I) hinterior)).symm

private theorem rack_membership {I : Instance}
    {final : PushFS.State (layout false I).width (layout false I).height}
    (hrack : line .south (layout false I).rackX final.boxes =
      line .south (layout false I).rackX (puzzle false I).initial.boxes)
    (p : Cell (layout false I).width (layout false I).height)
    (hx : p.1.val = (layout false I).rackX) (hp : p ∈ final.boxes) :
    p ∈ (puzzle false I).initial.boxes := by
  have hm : Direction.south.position p ∈ line .south (layout false I).rackX final.boxes :=
    mem_line.mpr ⟨p, hp, hx, rfl⟩
  rw [hrack] at hm
  obtain ⟨q, hq, hqx, hqpos⟩ := mem_line.mp hm
  have he : q = p := Direction.cell_ext .south (hqx.trans hx.symm) hqpos
  exact he ▸ hq

theorem ProbeWitness.marker_box {I : Instance}
    {final : PushFS.State (layout false I).width (layout false I).height}
    (W : ProbeWitness I final.boxesᶜ)
    (hsupport : Supported .east (layout false I).rackX final)
    (hrack : line .south (layout false I).rackX final.boxes =
      line .south (layout false I).rackX (puzzle false I).initial.boxes)
    {row : ℕ} (hrow : row ∈ (layout false I).markerRows)
    (p : Cell (layout false I).width (layout false I).height)
    (hx : p.1.val = (layout false I).rackX - 1) (hy : p.2.val = row) : p ∈ final.boxes := by
  have hread := W.run.parallel_read .east (probeQuotas I) row
  rw [marker_quotaAt I hrow] at hread
  have hrowfit : 0 < row ∧ row + 1 < (layout false I).height := by
    have hm := (layout false I).marker_mem hrow
    rcases Finset.mem_union.mp hm with hm | hm
    · have hi := (layout_fits false I).fixed_interior hm
      dsimp at hi
      omega
    · have he := congrArg Prod.snd (Finset.mem_singleton.mp hm)
      have hi := (layout false I).translated_bounds (stop_fit false I)
      dsimp at he
      omega
  have hP := (layout false I).rackX_ge
  have hnot := marker_probe_blocked I hread.eval hread.no_split (by
      intro q hq hborder hmem
      have hbefore := (Finset.mem_filter.mp hmem).1
      exact W.before_interior hbefore (Or.inr (Or.inl hborder))) (by
      intro q hq hqx hborder
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr ?_, ?_⟩, hq⟩
      · intro hb
        by_cases hcol : q.1.val = (layout false I).rackX
        · have hi := rack_membership hrack q hcol hb
          have hi := ((layout false I).mem_raster _ _).mp hi
          rw [hcol, hq, (layout false I).initialRaw_rack_iff] at hi
          exact marker_rack_empty I hrow hi
        · have hs := hsupport q hb
          change (q.1.val : ℤ) ≤ (layout false I).rackX at hs
          omega
      · intro hb
        have hb := (Finset.mem_filter.mp hb).2
        omega) p hy hx
  by_contra hp
  apply hnot
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hp, ?_⟩, hy⟩
  intro hb
  have hb := (Finset.mem_filter.mp hb).2
  unfold Layout.width at hb
  omega

private theorem ProbeWitness.region_agrees {I : Instance}
    {final : PushFS.State (layout false I).width (layout false I).height}
    (_W : ProbeWitness I final.boxesᶜ)
    (hsupport : Supported .east (layout false I).rackX final)
    (hrack : line .south (layout false I).rackX final.boxes =
      line .south (layout false I).rackX (puzzle false I).initial.boxes)
    (p : Cell (layout false I).width (layout false I).height)
    (hp : p ∈ readRegion .east (layout false I).probeRequests) :
    p ∈ final.boxesᶜ \ frameCells I ↔ p ∈ probeStart I := by
  obtain ⟨request, hr, hy, hx⟩ := (mem_readRegion _ _ p).mp hp
  simp only [Layout.probeRequests, List.mem_append, List.mem_map] at hr
  have hempty : p ∉ final.boxes ∧ p ∉ (layout false I).raster (layout false I).goalsRaw := by
    rcases hr with ⟨row, hrow, rfl⟩ | ⟨row, hrow, rfl⟩
    · have hpx : (layout false I).rackX < p.1.val := by
        simp only [prefixRank] at hx
        unfold Layout.width at hx
        omega
      constructor
      · intro hb
        have hs := hsupport p hb
        change (p.1.val : ℤ) ≤ (layout false I).rackX at hs
        omega
      · intro hb
        have hs := (layout false I).goalsRaw_west (((layout false I).mem_raster _ _).mp hb)
        omega
    · have hpx : (layout false I).rackX ≤ p.1.val := by
        simp only [prefixRank] at hx
        unfold Layout.width at hx
        omega
      constructor
      · intro hb
        by_cases hcol : p.1.val = (layout false I).rackX
        · have hi := rack_membership hrack p hcol hb
          have hi := ((layout false I).mem_raster _ _).mp hi
          rw [hcol, show p.2.val = row from hy, (layout false I).initialRaw_rack_iff] at hi
          exact marker_rack_empty I hrow hi
        · have hs := hsupport p hb
          change (p.1.val : ℤ) ≤ (layout false I).rackX at hs
          omega
      · intro hb
        have hraw := ((layout false I).mem_raster _ _).mp hb
        have hs := (layout false I).goalsRaw_west hraw
        have hcol : p.1.val = (layout false I).rackX := by omega
        rw [hcol, show p.2.val = row from hy, (layout false I).goalsRaw_rack_iff] at hraw
        exact marker_rack_empty I hrow hraw
  unfold probeStart
  rw [emit_remaining]
  have hregion : allRegions (w := (layout false I).width) (h := (layout false I).height)
      ((layout false I).quotaTemplates.take 3) = frameCells I := by
    ext p
    simpa only [frameCells, Finset.mem_filter, Finset.mem_univ, true_and, Boundary] using frame_region I p
  rw [hregion]
  simp only [Finset.mem_sdiff, Finset.mem_compl, Layout.referenceHoles, hempty.1, hempty.2,
    not_false_eq_true, true_and]

/-- Every accepted probe deletes exactly its literal geometric front. -/
theorem ProbeWitness.after_eq {I : Instance}
    {final : PushFS.State (layout false I).width (layout false I).height}
    (W : ProbeWitness I final.boxesᶜ)
    (hsupport : Supported .east (layout false I).rackX final)
    (hrack : line .south (layout false I).rackX final.boxes =
      line .south (layout false I).rackX (puzzle false I).initial.boxes) :
    W.after = (final.boxesᶜ \ frameCells I) \ readRegion .east (layout false I).probeRequests := by
  have heq := emit_rounds_agree [.read .east (layout false I).probeRequests]
    (final.boxesᶜ \ frameCells I) (probeStart I) (by
      intro p hp
      have hp' : p ∈ readRegion .east (layout false I).probeRequests := by
        simpa only [allRegions, Template.region, Finset.union_empty] using hp
      exact W.region_agrees hsupport hrack p hp')
  have hquotas : (emitReads .east (layout false I).probeRequests
      (final.boxesᶜ \ frameCells I)).quotas = probeQuotas I := by
    injection heq with hhead
    exact Round.read.inj hhead |>.2
  have he := emitReads_eval .east (layout false I).probeRequests (final.boxesᶜ \ frameCells I)
  rw [hquotas] at he
  have hf : W.after = (emitReads .east (layout false I).probeRequests
      (final.boxesᶜ \ frameCells I)).remaining := Option.some.inj (W.run.eval.symm.trans he)
  rw [hf, emitReads_remaining]

theorem ProbeWitness.neighbor_capacity {I : Instance}
    {final : PushFS.State (layout false I).width (layout false I).height}
    (W : ProbeWitness I final.boxesᶜ)
    (hsupport : Supported .east (layout false I).rackX final)
    (hrack : line .south (layout false I).rackX final.boxes =
      line .south (layout false I).rackX (puzzle false I).initial.boxes)
    {row : ℕ} (hrow : row ∈ (layout false I).dividerNeighbors)
    (p : Cell (layout false I).width (layout false I).height)
    (hp : p ∈ W.after) (hy : p.2.val = row) : 0 < p.1.val ∧ p.1.val < (layout false I).rackX := by
  rw [W.after_eq hsupport hrack] at hp
  obtain ⟨hbefore, hnot⟩ := Finset.mem_sdiff.mp hp
  have hi := W.before_interior hbefore
  have hP := (layout false I).rackX_ge
  constructor
  · simp only [Boundary, not_or] at hi
    omega
  · by_contra hcol
    have hrackRow : row ∈ (layout false I).rackProbeRows := by
      obtain ⟨g, hg, he⟩ := List.mem_flatMap.mp hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · apply List.mem_map.mpr
        refine ⟨((layout false I).rackX, g + (layout false I).shift - 1), ?_, rfl⟩
        apply List.mem_toFinset.mp
        change ((layout false I).rackX, g + (layout false I).shift - 1) ∈ (layout false I).rack
        exact (divider_rack_neighbors false I hg).1
      · apply List.mem_map.mpr
        refine ⟨((layout false I).rackX, g + (layout false I).shift + 1), ?_, rfl⟩
        apply List.mem_toFinset.mp
        change ((layout false I).rackX, g + (layout false I).shift + 1) ∈ (layout false I).rack
        exact (divider_rack_neighbors false I hg).2
    by_cases hx : p.1.val = (layout false I).rackX
    · exact Finset.mem_compl.mp (Finset.mem_sdiff.mp hbefore).1 (W.rack_box hsupport hrackRow p hx hy)
    · apply hnot
      apply (mem_readRegion _ _ p).mpr
      refine ⟨(row, (layout false I).width - (layout false I).rackX - 1),
        List.mem_append_left _ (List.mem_map.mpr ⟨row, hrackRow, rfl⟩), hy, ?_⟩
      simp only [prefixRank]
      unfold Layout.width
      have hw := p.1.isLt
      unfold Layout.width at hw
      omega

end PushPuzzle.PushPush.Doors.Source
