/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessProbeMask
public import Push.AcceptanceProgramProbeStock
import all Push.AcceptanceProgramProbeStock
import all Push.AcceptanceProgramProbeStockSignals
import all PushS.PortAxisFixed
import all PushS.PortSegments

/-! The actual non-main R13 probe stock is precisely the same target-independent fixed bitmap used by the emitted quotas. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe AcceptanceProgram

/-- Every literal fixed R13 probe cell lies off the main-axis family, including its two frame columns. -/
theorem probeFixedStock_not_main (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ probeFixedStock l p) : q.1 ∉ l.mainColumnSet p := by
  obtain ⟨hq, hrow⟩ := Finset.mem_filter.mp hq
  have hfixed := emit_remaining_subset _ _ hq
  have hs : Template.read .south [(0, p.H + 1), (p.W, p.H + 1)] ∈ probePrefix l p [] := by
    simp [probePrefix, preparation, frameSchedule]
  have hnot := emit_stage_excluded hs hq
  intro hmain
  rcases (l.mainColumnSet_iff p q.1).mp hmain with hx | hx | ⟨i, hi, hx⟩
  · apply hnot
    exact (mem_readRegion _ _ q).mpr ⟨(0, p.H + 1), by simp, hx, by
      change p.H - q.2.val < p.H + 1; omega⟩
  · apply hnot
    exact (mem_readRegion _ _ q).mpr ⟨(p.W, p.H + 1), by simp, hx, by
      change p.H - q.2.val < p.H + 1; omega⟩
  · obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hfixed
    have hpoint := (mem_pointHoles _ (q.1.val, q.2.val)).mpr ⟨s, hs, hc⟩
    have hloc := l.fixedSegments_on_main_axis p hl hM haxes hi hpoint hx
    obtain ⟨ref, href, _, hy⟩ := probe_row_data l p hrow
    obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM href
    have hY := readDepth_ge p hj hjm
    have hD := readDepth_add_lt_D p ref.level
    rw [readDepth_eq p hj hjm] at hY hD
    have h1 := readDepth_add_lt_D p 1
    have hH : p.H = 2 * p.D := rfl
    rcases hloc with h0 | hH' | ⟨_, hhalf⟩ <;> omega

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- At the genuine probe read, every non-main accepted hole is exactly a canonical fixed-stock cell. -/
theorem canonical_probe_nonmain_fixed_iff
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hrow : q.2.val ∈ probeRows l p) (hnmain : q.1 ∉ l.mainColumnSet p) :
    q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 13 ↔ q ∈ probeFixedStock l p := by
  have hreference := schedule_probe_stock l p hl hM haxes target
  have href := canonical_probe_nonmain_reference l p hl hM haxes initial target hgate hr ha hrow hnmain
  constructor
  · intro hq
    have hm := (congrArg (fun S : Finset (Cell (p.W + 1) (p.H + 1)) => q ∈ S) hreference).mp
      (Finset.mem_filter.mpr ⟨href.mp hq, hrow⟩)
    rcases Finset.mem_union.mp hm with hfixed | hsignal
    · exact hfixed
    · obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hsignal
      have hx := congrArg (fun q : Cell (p.W + 1) (p.H + 1) => q.1.val) hi
      change p.x i.val = q.1.val at hx
      exact (hnmain ((l.mainColumnSet_iff p q.1).mpr (Or.inr (Or.inr ⟨i.val, i.isLt, hx.symm⟩)))).elim
  · intro hq
    have hm := (congrArg (fun S : Finset (Cell (p.W + 1) (p.H + 1)) => q ∈ S) hreference).mpr
      (Finset.mem_union_left _ hq)
    exact href.mpr (Finset.mem_filter.mp hm).1

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
