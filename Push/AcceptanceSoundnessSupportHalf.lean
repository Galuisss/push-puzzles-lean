/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportHalfRead
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram

/-! The actual half-depth horizontal quota saturates precisely the surviving gate-core marker stock. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- Every core half-depth marker is present immediately before the real half-row read. -/
theorem canonical_core_half_marker_input (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - p.Y 1 / 2) (hx : q.1.val ∈ cores l p) :
    q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 26 := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  let F := roundResidual stages T E 26
  let R := (emit (stages.take 26) T).remaining
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi : stages[26]? = some (readRows p .west {p.H - p.Y 1 / 2}) := by
    simp only [stages, schedule, preparation, frameSchedule, pageChecks,
      ite_true, reduceCtorEq, ite_false, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have he := (roundResidual_step stages T E 26 hc hi).1
  have hstock : (F.filter fun b => b.2.val ∈ ({p.H - p.Y 1 / 2} : Finset ℕ)) ⊆
      R.filter fun b => b.2.val ∈ ({p.H - p.Y 1 / 2} : Finset ℕ) := by
    intro b hb
    obtain ⟨hb, hby⟩ := Finset.mem_filter.mp hb
    have hby := Finset.mem_singleton.mp hby
    exact Finset.mem_filter.mpr ⟨core_half_remaining l p hl hM haxes target hby
      (canonical_half_input_core_stock l p hl hM haxes initial target hr ha hb hby), Finset.mem_singleton.mpr hby⟩
  have hsat := row_saturation p .west {p.H - p.Y 1 / 2} (Or.inl rfl) R F hstock ⟨_, he⟩
  exact hsat (Finset.mem_filter.mpr ⟨core_half_remaining l p hl hM haxes target hy hx, Finset.mem_singleton.mpr hy⟩)

/-- Every actual gate-core half-depth marker is a hole at the accepted endpoint. -/
theorem canonical_core_half_marker_terminal (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - p.Y 1 / 2) (hx : q.1.val ∈ cores l p) : q ∈ PushS.holes t := by
  have hq := canonical_core_half_marker_input l p hl hM haxes initial target hr ha hy hx
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  exact scan_subset (roundResidual_eval _ _ _ 26 hc) hq

end PushPuzzle.Push.AcceptanceSoundness
