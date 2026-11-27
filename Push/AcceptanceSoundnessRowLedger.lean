/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessFWalk
public import Push.AcceptanceProgramProbeStock
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramRegions
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all Push.AcceptanceProgramWorkClear
import all PushFS.Grid

/-! The actual full-row reads and their zero-loss clears impose the exact canonical row budgets. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

private theorem row_reference_cleared (p : Scales.Parameters) (rows : Finset ℕ) (row : ℕ)
    (hrow : row ∈ rows) (T : Finset (Cell (p.W + 1) (p.H + 1))) :
    ((emit [readRows p .west rows] T).remaining.filter fun q => q.2.val = row) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  obtain ⟨hq, hy⟩ := Finset.mem_filter.mp hq
  apply emit_stage_excluded (List.mem_cons_self ..) hq
  exact (readRows_region p .west rows (Or.inl rfl) q).mpr (hy ▸ hrow)

/-- If an actual whole-row block exhausts a selected row, its input row has exactly the emitted reference quota. -/
private theorem row_read_input_card (p : Scales.Parameters) (rows : Finset ℕ) (row : ℕ)
    (hrow : row ∈ rows)
    (T E F : Finset (Cell (p.W + 1) (p.H + 1)))
    (he : Scan.eval (instructions (emit [readRows p .west rows] T).rounds) E = some F)
    (hF : (F.filter fun q => q.2.val = row) = ∅) :
    (E.filter fun q => q.2.val = row).card = (T.filter fun q => q.2.val = row).card := by
  have hloss := round_reference_lane_loss .west (prefixRequests rows fun _ => p.W + 1) T E F row he
  change (E.filter fun q => q.2.val = row).card +
    ((emit [readRows p .west rows] T).remaining.filter fun q => q.2.val = row).card =
      (F.filter fun q => q.2.val = row).card + (T.filter fun q => q.2.val = row).card at hloss
  simpa only [row_reference_cleared p rows row hrow T, hF, Finset.card_empty, Nat.add_zero, Nat.zero_add] using hloss

/-- The real probe-row read must exactly pay its canonical input inventory, because the next actual clear loses zero holes. -/
private theorem canonical_probe_row_input_card (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (row : ℕ) (hrow : row ∈ probeRows l p) :
    ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 13).filter fun q => q.2.val = row).card =
      (((emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 13)
        (targetHoles l p target)).remaining).filter fun q => q.2.val = row).card := by
  let T := targetHoles l p target
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi13 : stages[13]? = some (readRows p .west (probeRows l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hi14 : stages[14]? = some (.clear .east (probeRows l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have he := (roundResidual_step stages T (PushS.holes t) 13 hc hi13).1
  have hF : ((roundResidual stages T (PushS.holes t) 14).filter fun q => q.2.val = row) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro q hq
    obtain ⟨hq, hy⟩ := Finset.mem_filter.mp hq
    have hkeep := (roundResidual_clear_keeps stages T (PushS.holes t) 14 hc hi14 hq).2
    change q.2.val ∉ probeRows l p at hkeep
    exact hkeep (hy ▸ hrow)
  exact row_read_input_card p (probeRows l p) row hrow _ _ _ he hF

/-- Every actual selected probe level pays the fixed physical stock plus its complete target-bit sum. -/
theorem canonical_probe_row_target_ledger (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels) (hrow : p.Y j + 2 ∈ probeRows l p) :
    ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 13).filter fun q => q.2.val = p.Y j + 2).card =
      ((probeFixedStock l p).filter fun q => q.2.val = p.Y j + 2).card +
        ∑ i ∈ Finset.univ.filter (fun i : Fin l.portCount => AcceptanceProbe.level l hl i = j),
          (target.getD i.val false).toNat := by
  rw [canonical_probe_row_input_card l p hl hM haxes initial target hr ha _ hrow]
  exact schedule_probe_row_card l p hl hM haxes target hj hjm hrow

/-- After the final actual working-row read, no working-row hole remains for a later page check to pay. -/
private theorem canonical_work_row_read_cleared (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 24).filter fun q => q.2.val ∈ workRows l p) = ∅ := by
  let T := targetHoles l p target
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi24 : stages[24]? = some (.clear .north (Finset.range (p.W + 1) \ (auxiliaries l p ∪ cores l p))) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  obtain ⟨hq, hrow⟩ := Finset.mem_filter.mp hq
  have hq25 := (roundResidual_clear_keeps stages T (PushS.holes t) 24 hc hi24 hq).1
  have hcut := canonical_page_residual_rows l p hl hM haxes initial target hr ha hq25
  exact Finset.disjoint_left.mp (cutRows_disjoint_workRows l p) hcut hrow

/-- The actual final working-row block pays exactly the canonical reference inventory on every selected row. -/
theorem canonical_work_row_input_card (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (row : ℕ) (hrow : row ∈ workRows l p \ ({0, p.H} ∪ probeRows l p)) :
    ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 23).filter fun q => q.2.val = row).card =
      (((emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 23)
        (targetHoles l p target)).remaining).filter fun q => q.2.val = row).card := by
  let T := targetHoles l p target
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi23 : stages[23]? = some (readRows p .west (workRows l p \ ({0, p.H} ∪ probeRows l p))) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have he := (roundResidual_step stages T (PushS.holes t) 23 hc hi23).1
  have hclear := canonical_work_row_read_cleared l p hl hM haxes initial target hr ha
  have hF : ((roundResidual stages T (PushS.holes t) 24).filter fun q => q.2.val = row) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro q hq
    obtain ⟨hq, hy⟩ := Finset.mem_filter.mp hq
    apply Finset.notMem_empty q
    rw [← hclear]
    exact Finset.mem_filter.mpr ⟨hq, hy ▸ (Finset.mem_sdiff.mp hrow).1⟩
  exact row_read_input_card p _ row hrow _ _ _ he hF

end PushPuzzle.Push.AcceptanceSoundness
