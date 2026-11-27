/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportTrimDepth
import all Push.AcceptanceSoundnessSupportCutUnique
import all Push.AcceptanceProgramLayout

/-! The first real lower finishing round excludes lower holes from every nonlive column already at its input. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- On an auxiliary column outside the lower live stock, the actual pre-page-check residual is already north of the cut. -/
theorem canonical_nonlive_lower_depth_le_cut (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 25)
    (hx : q.1.val ∈ auxiliaries l p) (hn : q.1.val ∉ lowerLiveColumns l p) : q.2.val ≤ p.D := by
  let g : Cell (p.W + 1) (p.H + 1) := (q.1, ⟨p.D, by have : p.H = 2 * p.D := rfl; omega⟩)
  have hg : g ∈ l.centralMarkers p := auxiliary_central_marker l p (q := g) hx rfl
  obtain ⟨pay, hsouth, hinput, _⟩ := canonical_cut_lower_exhausted l p hl hM haxes initial target hr ha hg rfl
  have hhead : pageCheckStages l p =
      [] ++ lowerFinish p (auxiliaries l p \ live l p .lower) :: (pageCheckStages l p).tail := rfl
  have hfirst : southReadsColumn q.1.val (lowerFinish p (auxiliaries l p \ live l p .lower)) := by
    rw [southReadsColumn_finish]
    exact decide_eq_true (Finset.mem_sdiff.mpr ⟨hx, hn⟩)
  have hpay : southReadsColumn q.1.val (.read pay.side pay.requests) := by
    obtain ⟨request, hrequest, he⟩ := pay.on_line
    simp only [hsouth, Direction.lane] at he
    simp only [hsouth, southReadsColumn, List.any_eq_true]
    exact ⟨request, hrequest, by simpa only [beq_iff_eq] using he.symm⟩
  have hbefore := unique_split_prefix _ (southReadsColumn q.1.val)
    (pageCheck_south_column_count_le_one l p hl q.1.val)
    pay.before pay.after [] (pageCheckStages l p).tail _ _ pay.split hhead hpay hfirst
  have he := pay.prefix_eval
  rw [hbefore] at he
  change some (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
    (targetHoles l p target) (PushS.holes t) 25) = some pay.input at he
  exact hinput q (Option.some.inj he ▸ hq) rfl

end PushPuzzle.Push.AcceptanceSoundness
