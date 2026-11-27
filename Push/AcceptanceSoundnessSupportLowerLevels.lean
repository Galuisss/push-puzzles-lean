/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportPagePositions
import all Push.AcceptanceSoundnessSupportCutUnique
import all Push.AcceptanceProgramLayout

/-! Actual lower finishes empty their columns before every deeper lower marker-row check. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- After a column's own real lower finish, every surviving hole in that column is strictly above the cut. -/
theorem canonical_lower_level_finished_empty (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {a : PageColumn} (hac : a ∈ pageColumns l p .lower) (hj : 1 ≤ a.level) (hjm : a.level < p.levels)
    (n : ℕ) (hn : 2 * a.level + 3 ≤ n) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ pageResidual l p target (PushS.holes t) n) (hx : q.1.val = a.column) : q.2.val < p.D := by
  let g : Cell (p.W + 1) (p.H + 1) := (q.1, ⟨p.D, by have : p.H = 2 * p.D := rfl; omega⟩)
  have hg : g ∈ l.centralMarkers p := auxiliary_central_marker l p (q := g)
    (hx ▸ l.acceptancePageColumn_aux p hl hM haxes .lower hac) rfl
  obtain ⟨pay, hsouth, _, houtput⟩ := canonical_cut_lower_exhausted l p hl hM haxes initial target hr ha hg rfl
  have hi := (pageCheck_lower_level_positions l p hj hjm).2
  have hcol : g.1.val ∈ lowerLevelColumns l p a.level := by
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨hac, by simp⟩, hx.symm⟩)
  have hbefore := pageCheck_south_payment_before_at l p hl pay hsouth (2 * a.level + 2) _ hi hcol
  have hlen : pay.before.length = 2 * a.level + 2 := by
    rw [hbefore, List.length_take]
    apply Nat.min_eq_left
    exact Nat.le_of_lt (List.getElem?_eq_some_iff.mp hi).1
  have hc := (canonical_page_check_execution l p hl hM haxes initial target hr ha).2
  have hqout : q ∈ pay.output := by
    rw [pay.output_roundResidual]
    apply roundResidual_antitone _ _ _ hc (show pay.before.length + 1 ≤ n by omega)
    exact hq
  exact houtput q hqout rfl

/-- The literal lower core clear removes every gate-core column from all later actual page residuals. -/
theorem canonical_core_page_residual_empty (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (n : ℕ) (hn : 3 ≤ n) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ pageResidual l p target (PushS.holes t) n) : q.1.val ∉ cores l p := by
  have hc := (canonical_page_check_execution l p hl hM haxes initial target hr ha).2
  have hi : (pageCheckStages l p)[2]? = some (.clear .north (cores l p)) := rfl
  have hq2 := roundResidual_antitone _ _ _ hc (show 2 ≤ n by omega) hq
  exact (roundResidual_clear_keeps _ _ _ 2 hc hi hq2).2

end PushPuzzle.Push.AcceptanceSoundness
