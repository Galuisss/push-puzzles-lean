/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWideNorth
public import Push.AcceptanceSoundnessGuardRow
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all PushFS.Grid

/-! The later actual south guard read saturates the disjoint remaining lower fixed stock. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- Complete canonical strict-interior stock below the upper guard marker. -/
def guardSouthStock (l : PortLayout) (p : Scales.Parameters) (target : List Bool) (x : ℕ) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  (targetHoles l p target \ Boundary.frame).filter fun q => q.1.val = x ∧ p.D - 4 < q.2.val

/-- The actual full south read pays exactly the complete lower stock of a selected wide-separator column. -/
theorem canonical_guard_south_paid_of_target_stock (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (x : Fin (p.W + 1)) (hx : x.val ∈ guards l p)
    (hsource : ∀ q ∈ PushS.holes t, q ∉ Boundary.frame → q.1 = x → q ∈ targetHoles l p target) :
    guardSouthStock l p target x.val =
      ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 19).filter fun q => q.1.val = x.val) \
      ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 20).filter fun q => q.1.val = x.val) := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  let R := (emit (stages.take 19) T).remaining
  let A := roundResidual stages T E 19
  let F := roundResidual stages T E 20
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi : stages[19]? = some (readColumns p .south (guards l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have he := (roundResidual_step stages T E 19 hc hi).1
  have hstock : A.filter (fun q => Direction.south.lane q = x.val) \
      F.filter (fun q => Direction.south.lane q = x.val) ⊆ guardSouthStock l p target x.val := by
    intro q hq
    obtain ⟨hqA, _⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hqA, hqx⟩ := Finset.mem_filter.mp hqA
    have hqx : q.1.val = x.val := hqx
    have hf := canonical_residual_not_frame l p hl hM haxes initial target hr ha 19 (by omega) hqA
    have hqE := scan_subset (roundResidual_eval stages T E 19 hc) hqA
    have htarget := hsource q hqE hf (Fin.ext hqx)
    have hdepth : p.D - 4 < q.2.val := by
      by_contra hn
      by_cases hlt : q.2.val < p.D - 4
      · have hqStock : q ∈ guardNorthStock l p target x.val :=
          Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨htarget, hf⟩, hqx, hlt⟩
        rw [canonical_guard_north_paid_of_target_stock l p hl hM haxes initial target hr ha x hx hsource] at hqStock
        exact (Finset.mem_sdiff.mp hqStock).2 (Finset.mem_filter.mpr
          ⟨roundResidual_antitone stages T E hc (by omega : 12 ≤ 19) hqA, hqx⟩)
      · have heq : q.2.val = p.D - 4 := by omega
        have hq13 := roundResidual_antitone stages T E hc (by omega : 13 ≤ 19) hqA
        have hclear := canonical_guard_row_cleared l p hl hM haxes initial target hr ha
        exact Finset.notMem_empty q (hclear ▸ Finset.mem_filter.mpr ⟨hq13, heq⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨htarget, hf⟩, hqx, hdepth⟩
  have hwhole : R.filter (fun q => Direction.south.lane q = x.val ∧ prefixRank .south q < p.H + 1) =
      R.filter (fun q => q.1.val = x.val) := by
    apply Finset.filter_congr
    intro q _
    simp only [Direction.lane, prefixRank, Nat.add_sub_cancel]
    omega
  have hfront : R.filter (fun q => Direction.south.lane q = x.val ∧ prefixRank .south q < p.H + 1) =
      guardSouthStock l p target x.val :=
    hwhole.trans (guard_south_stock_eq l p hl hM haxes target x.val hx)
  have href := prefix_round_reference_card .south (guards l p) (fun _ => p.H + 1) R x.val hx
  rw [hfront] at href
  exact round_lane_saturation .south (prefixRequests (guards l p) fun _ => p.H + 1) R A F
    (guardSouthStock l p target x.val) x.val he hstock href.le

/-- The actual read saturates the selected wide-separator column using its proven distant-source stock. -/
theorem canonical_wide_guard_south_paid (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {g : Cell (p.W + 1) (p.H + 1)} (hg : g ∈ l.wideSeparatorHoles p) (hx : g.1.val ∈ guards l p) :
    guardSouthStock l p target g.1.val =
      ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 19).filter fun q => q.1.val = g.1.val) \
      ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 20).filter fun q => q.1.val = g.1.val) := by
  exact canonical_guard_south_paid_of_target_stock l p hl hM haxes initial target hr ha g.1 hx
    (fun q hq hf hqx => canonical_wide_column_target_stock l p hl hM haxes initial target hr ha hg hqx hq hf)

end PushPuzzle.Push.AcceptanceSoundness
