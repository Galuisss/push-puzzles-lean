/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessProbeColumns
public import Push.AcceptanceProgramGateAxisReadStock
public import Push.AcceptanceGateAxisInventory
import all Push.AcceptanceSoundnessSupportCoordinates
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all PushS.Scales

/-! The true third row clear excludes the gate's nearest pre-work hole after the combined axis read. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

private theorem thirdRowKeep_even (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hr : q.2.val ∈ thirdRowKeep l p) : q.2.val % 2 = 0 := by
  change q.2.val ∈ workRows l p ∪ cutRows p ∪ {p.D + 4} at hr
  rcases Finset.mem_union.mp hr with hr | hr
  · rcases Finset.mem_union.mp hr with hr | hr
    · exact l.workingRowSet_even p ((working_rows_iff l p q.2).mp hr)
    · exact cut_rows_even p hr
  · have hD : p.D % 2 = 0 := by simp [Scales.Parameters.D, Scales.Parameters.A, Scales.Parameters.Q, Nat.mul_mod]
    have he := Finset.mem_singleton.mp hr
    omega

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

/-- The actual R16 input contains no hole at the odd row immediately above the lower gate work row. -/
theorem canonical_gate_last_not_residual_sixteen {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - (p.Y 1 + 1)) :
    q ∉ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 16 := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have i16 : stages[16]? = some (.clear .north (axes l p \ cores l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have i17 : stages[17]? = some (.clear .west (Finset.range (p.H + 1) \ thirdRowKeep l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, thirdRowKeep, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  intro hq
  have hq17 := (roundResidual_clear_keeps stages T E 16 hc i16 hq).1
  have hkeep := (roundResidual_clear_keeps stages T E 17 hc i17 hq17).2
  change q.2.val ∉ Finset.range (p.H + 1) \ thirdRowKeep l p at hkeep
  have hykeep : q.2.val ∈ thirdRowKeep l p := by
    by_contra hn
    exact hkeep (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr q.2.isLt, hn⟩)
  have heven := thirdRowKeep_even l p hykeep
  have hH : p.H % 2 = 0 := by simp [Scales.Parameters.H]
  have hY : p.Y 1 % 2 = 0 := by simp [Scales.Parameters.Y, Scales.Parameters.A, Scales.Parameters.Q, Nat.mul_mod]
  have hYH := readDepth_add_lt_H p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hYH
  omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
