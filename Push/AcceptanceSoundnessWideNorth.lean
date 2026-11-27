/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWideSaturation
public import Push.AcceptanceProgramGuardStockReads
import all Push.AcceptanceSoundnessSupportGuardBarrier
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all PushFS.Grid

/-! The real north guard read saturates each globally distant column's complete upper fixed stock. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- Complete canonical strict-interior stock above the upper guard marker in one actual column. -/
def guardNorthStock (l : PortLayout) (p : Scales.Parameters) (target : List Bool) (x : ℕ) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  (targetHoles l p target \ Boundary.frame).filter fun q => q.1.val = x ∧ q.2.val < p.D - 4

/-- The true north guard read pays exactly the entire upper stock on every selected wide-separator column. -/
theorem canonical_guard_north_paid_of_target_stock (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (x : Fin (p.W + 1)) (hx : x.val ∈ guards l p)
    (hsource : ∀ q ∈ PushS.holes t, q ∉ Boundary.frame → q.1 = x → q ∈ targetHoles l p target) :
    guardNorthStock l p target x.val =
      ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 11).filter fun q => q.1.val = x.val) \
      ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 12).filter fun q => q.1.val = x.val) := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  let R := (emit (stages.take 11) T).remaining
  let A := roundResidual stages T E 11
  let F := roundResidual stages T E 12
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi : stages[11]? = some (.read .north (prefixRequests (guards l p) fun _ => p.D - 4)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have he := (roundResidual_step stages T E 11 hc hi).1
  obtain ⟨marker, hmx, hmy, hm⟩ := actual_guard_marker l p x hx
  have hm12 := guard_markers_residual l p hl hM haxes initial target hr
    (canonical_initial_frame l p hl hM haxes initial target)
    (canonical_initial_holes l p hl hM haxes initial target) ha hm hmy
  have hstock : A.filter (fun q => Direction.north.lane q = x.val) \
      F.filter (fun q => Direction.north.lane q = x.val) ⊆ guardNorthStock l p target x.val := by
    intro q hq
    obtain ⟨hqA, hqF⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hqA, hqx⟩ := Finset.mem_filter.mp hqA
    have hqx : q.1.val = x.val := hqx
    have hqF' : q ∉ F := fun h => hqF (Finset.mem_filter.mpr ⟨h, hqx⟩)
    have hlt := round_deleted_before_retained .north _ _ he hm12 hqA hqF'
      ((congrArg Fin.val hmx).trans hqx.symm)
    have hf := canonical_residual_not_frame l p hl hM haxes initial target hr ha 11 (by omega) hqA
    have hqE := scan_subset (roundResidual_eval stages T E 11 hc) hqA
    have htarget := hsource q hqE hf (Fin.ext hqx)
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨htarget, hf⟩, hqx, by
      simpa only [prefixRank, hmy] using hlt⟩
  have hfront : R.filter (fun q => Direction.north.lane q = x.val ∧ prefixRank .north q < p.D - 4) =
      guardNorthStock l p target x.val := guard_north_front_eq l p hl hM haxes target x.val hx
  have href := prefix_round_reference_card .north (guards l p) (fun _ => p.D - 4) R x.val hx
  rw [hfront] at href
  exact round_lane_saturation .north (prefixRequests (guards l p) fun _ => p.D - 4) R A F
    (guardNorthStock l p target x.val) x.val he hstock href.le

/-- The actual read saturates the selected wide-separator column using its proven distant-source stock. -/
theorem canonical_wide_guard_north_paid (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {g : Cell (p.W + 1) (p.H + 1)} (hg : g ∈ l.wideSeparatorHoles p) (hx : g.1.val ∈ guards l p) :
    guardNorthStock l p target g.1.val =
      ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 11).filter fun q => q.1.val = g.1.val) \
      ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 12).filter fun q => q.1.val = g.1.val) := by
  exact canonical_guard_north_paid_of_target_stock l p hl hM haxes initial target hr ha g.1 hx
    (fun q hq hf hqx => canonical_wide_column_target_stock l p hl hM haxes initial target hr ha hg hqx hq hf)

end PushPuzzle.Push.AcceptanceSoundness
