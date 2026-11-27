/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportGuardBarrier
public import Push.AcceptanceSoundnessSupportClean
import all Push.AcceptanceSoundnessCentralGuard
import all Push.AcceptanceSoundnessCentralFlanks
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceSoundnessFrame
import all Push.AcceptanceProgramRounds
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all Push.AcceptanceProgramNarrowSignals
import all Push.AcceptanceProgramNarrowFixed
import all Push.AcceptanceProgramStock
import all Push.Scan

/-! The actual guard-marker row has no residual holes after its complete horizontal payment. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- A full horizontal row read clears its row whenever its actual input stock fits the reference row. -/
theorem row_saturation_clears (p : Scales.Parameters) (side : Direction) (row : ℕ)
    (hside : side = .west ∨ side = .east) (T E F : Finset (Cell (p.W + 1) (p.H + 1)))
    (hstock : (E.filter fun q => q.2.val = row) ⊆ T.filter fun q => q.2.val = row)
    (he : Scan.eval (instructions (emit [readRows p side {row}] T).rounds) E = some F) :
    (F.filter fun q => q.2.val = row) = ∅ := by
  have hcount : (T.filter fun q => q ∈ (Scan.lineCells side row).take (p.W + 1)).card =
      (T.filter fun q => q.2.val = row).card := by
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro q _
    rw [mem_line_prefix]
    rcases hside with rfl | rfl
    · change (q.2.val = row ∧ q.1.val < p.W + 1) ↔ q.2.val = row
      exact and_iff_left q.1.isLt
    · change (q.2.val = row ∧ p.W + 1 - 1 - q.1.val < p.W + 1) ↔ q.2.val = row
      have hq := q.1.isLt
      omega
  have hread : (Scan.Instruction.read side row (T.filter fun q => q.2.val = row).card).eval E = some F := by
    simpa only [readRows, prefixRequests, Finset.sort_singleton, List.map_cons, List.map_nil,
      emit, emitReads, instructions, List.flatMap_cons, List.flatMap_nil, Round.instructions,
      List.append_nil, Scan.eval, Option.bind_some, Option.bind_fun_some, hcount] using he
  have hline := Scan.Instruction.read_line_card hread
  have hle := Finset.card_le_card hstock
  apply Finset.card_eq_zero.mp
  rcases hside with rfl | rfl <;> change
    (F.filter fun q => q.2.val = row).card + (T.filter fun q => q.2.val = row).card =
      (E.filter fun q => q.2.val = row).card at hline <;> omega

private theorem guardBefore_eq_take_twelve (l : PortLayout) (p : Scales.Parameters) (target : List Bool) :
    (schedule l p (targetHoles l p target \ Boundary.frame).card).take 12 = guardBefore l p target := by
  rfl

/-- The actual thirteenth-round residual has no hole on the fully paid `D−4` guard-marker row. -/
theorem canonical_guard_row_cleared (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 13).filter fun q => q.2.val = p.D - 4) = ∅ := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hs0 := canonical_initial_holes l p hl hM haxes initial target
  have hp0 := canonical_initial_frame l p hl hM haxes initial target
  have hc := (program_clean_execution l p hl hM haxes initial target hr hs0 ha).2
  have hi : stages[12]? = some (readRows p .west {p.D - 4}) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have he := (roundResidual_step stages T E 12 hc hi).1
  have htake3 : stages.take 3 = sideClearSchedule l p target := by
    simp only [stages, schedule, preparation, frameSchedule, sideClearSchedule, T,
      List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero]
  have htake12 : stages.take 12 = guardBefore l p target := guardBefore_eq_take_twelve l p target
  apply row_saturation_clears p .west (p.D - 4) (Or.inl rfl) _ _ _ _ he
  intro q hq
  obtain ⟨hq, hy⟩ := Finset.mem_filter.mp hq
  have hqE := scan_subset (roundResidual_eval stages T E 12 hc) hq
  have hf : q ∉ Boundary.frame := by
    have hq3 := roundResidual_antitone stages T E hc (by omega : 3 ≤ 12) hq
    unfold roundResidual at hq3
    rw [htake3, program_sideClear_eval l p target ha, Option.getD_some,
      program_sideClear_remaining l p hl hM haxes initial target hr hs0 ha] at hq3
    exact (Finset.mem_sdiff.mp hq3).2
  have hnew := program_new_rows_stock l p hl hM haxes initial target hr hp0 hs0 ha hqE hf
    (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr (Or.inr (Or.inl hy)))
  apply Finset.mem_filter.mpr
  rw [htake12]
  exact ⟨guard_target_kept l p hl hM haxes target (newCentralMarkers_subset l p hnew) hy, hy⟩

end PushPuzzle.Push.AcceptanceSoundness
