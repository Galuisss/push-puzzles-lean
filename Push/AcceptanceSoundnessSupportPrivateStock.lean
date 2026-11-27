/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportPrivateBarrier
public import Push.AcceptanceProgramPrivateStock
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentralGeometry
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all PushS.PortWalkBudget

/-! Every actual private-cap payment lies in its column's four canonical positions. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- The four actual depths available to a private-column payment after the second row clear. -/
def privateDepths (p : Scales.Parameters) : Finset ℕ := {p.Y 1 / 2, p.Y 1, p.Y 1 + 1, p.Y 1 + 2}

/-- The finite physical four-position private window on one column. -/
def privateSlots (p : Scales.Parameters) (x : Fin (p.W + 1)) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  Finset.univ.filter fun q => q.1 = x ∧ pageDepth p .lower q ∈ privateDepths p

/-- A private column has at most one physical cell at each of the four selected depths. -/
theorem privateSlots_card_le_four (p : Scales.Parameters) (x : Fin (p.W + 1)) :
    (privateSlots p x).card ≤ 4 := by
  have hcard : (privateSlots p x).card ≤ (privateDepths p).card := by
    apply Finset.card_le_card_of_injOn (pageDepth p .lower)
    · intro q hq
      exact (Finset.mem_filter.mp hq).2.2
    · intro a ha b hb he
      have hax := (Finset.mem_filter.mp ha).2.1
      have hbx := (Finset.mem_filter.mp hb).2.1
      apply Prod.ext (hax.trans hbx.symm)
      apply Fin.ext
      have haH := a.2.isLt
      have hbH := b.2.isLt
      change p.H - a.2.val = p.H - b.2.val at he
      omega
  exact hcard.trans Finset.card_le_four

/-- The lower sample marker row never supplies a real hole on a genuine private column. -/
private theorem canonical_private_not_sample_row (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ privateColumns l p)
    (hq : q ∈ PushS.holes t) (hf : q ∉ Boundary.frame) : q.2.val ≠ p.D + 4 := by
  intro hy
  have hm := program_new_rows_stock l p hl hM haxes initial target hr
    (canonical_initial_frame l p hl hM haxes initial target)
    (canonical_initial_holes l p hl hM haxes initial target) ha hq hf (by simp [hy])
  obtain ⟨i, hi, hix⟩ := sample_marker_source l p (newCentralMarkers_subset l p hm) hy
  have hsample : q.1.val ∈ samples l p := by
    apply List.mem_toFinset.mpr
    apply List.mem_flatMap.mpr
    exact ⟨i, hi, by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hix⟩
  obtain ⟨a, hac, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  exact l.acceptanceLowerColumn_not_sample p hl (List.mem_filter.mp hac).1 (he ▸ hsample)

/-- The actual private read pays only the four physical positions permitted by its preceding clear and retained first marker. -/
theorem canonical_private_payment_slot (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ privateColumns l p)
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 9)
    (hqout : q ∉ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 10) : q ∈ privateSlots p q.1 := by
  have hrows := canonical_private_input_rows l p hl hM haxes initial target hr ha hq
  have hf := canonical_residual_not_frame l p hl hM haxes initial target hr ha 9 (by omega) hq
  have hbottom : q.2.val ≠ p.H := by
    intro hb
    exact hf ((Boundary.mem_frame q).mpr ⟨.south, by simp [Boundary.edge, hb]⟩)
  have hdepth := canonical_private_payment_depth l p hl hM haxes initial target hr ha hx hq hqout
  rcases privateColumn_window l p hx hrows hbottom hdepth with hwindow | hsample
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hwindow⟩
  · have hc := (program_clean_execution l p hl hM haxes initial target hr
      (canonical_initial_holes l p hl hM haxes initial target) ha).2
    exact False.elim (canonical_private_not_sample_row l p hl hM haxes initial target hr ha hx
      (scan_subset (roundResidual_eval _ _ _ 9 hc) hq) hf hsample)

end PushPuzzle.Push.AcceptanceSoundness
