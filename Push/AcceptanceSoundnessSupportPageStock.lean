/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportSouthCut
import all Push.AcceptanceSoundnessSupportLanes
import all Push.AcceptanceProgramLayout

/-! All actual holes left after working-row checks lie on genuine marker-check rows. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

private theorem cutRows_interlevel (p : Scales.Parameters) {k : ℕ} (hk : k ∈ List.range (p.levels - 1)) :
    (p.Y (k + 1) + p.Y (k + 2)) / 2 ∈ cutRows p ∧
      p.H - (p.Y (k + 1) + p.Y (k + 2)) / 2 ∈ cutRows p := by
  constructor
  all_goals
    apply List.mem_toFinset.mpr
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    exact ⟨k, hk, by simp⟩

private theorem pageCheck_payment_row (l : PortLayout) (p : Scales.Parameters)
    {side : Direction} {requests : List (ℕ × ℕ)}
    (hstage : Template.read side requests ∈ pageCheckStages l p)
    {q : Cell (p.W + 1) (p.H + 1)} (ht : ReadTouches (.read side requests) q) :
    side = .south ∨ q.2.val ∈ cutRows p := by
  simp only [pageCheckStages, pageChecks, ite_true, reduceCtorEq, ite_false, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hstage
  rcases hstage with (hhead | hlevels) | (hhead | hlevels)
  · rcases hhead with he | he
    · cases he
      exact Or.inl rfl
    · cases he
      have hy := Finset.mem_singleton.mp (row_touches p .west _ (Or.inl rfl) ht)
      exact Or.inr (by simp [cutRows, hy])
  · obtain ⟨k, hk, hmem⟩ := List.mem_flatMap.mp hlevels
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with he | he
    · cases he
      have hy := Finset.mem_singleton.mp (row_touches p .west _ (Or.inl rfl) ht)
      exact Or.inr (hy.symm ▸ (cutRows_interlevel p hk).2)
    · cases he
      exact Or.inl rfl
  · exact hhead.elim
  · obtain ⟨k, hk, hmem⟩ := List.mem_flatMap.mp hlevels
    simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at hmem
    cases hmem
    have hy := Finset.mem_singleton.mp (row_touches p .west _ (Or.inl rfl) ht)
    exact Or.inr (hy.symm ▸ (cutRows_interlevel p hk).1)

/-- The actual accepted residual after all working checks contains holes only on emitted central, half-depth, or interlevel check rows. -/
theorem canonical_page_residual_rows (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 25) : q.2.val ∈ cutRows p := by
  have he := canonical_page_check_execution l p hl hM haxes initial target hr ha
  obtain ⟨pay⟩ := round_payment _ _ _ he.1 he.2 hq
  have hstage : Template.read pay.side pay.requests ∈ pageCheckStages l p :=
    (congrArg (fun stages : List Template => Template.read pay.side pay.requests ∈ stages)
      pay.split).mpr (List.mem_append_right _ (List.mem_cons_self ..))
  rcases pageCheck_payment_row l p hstage pay.on_line with hsouth | hrow
  · have hy := canonical_page_south_payment_cut l p hl hM haxes initial target hr ha pay hsouth
    simp [cutRows, hy]
  · exact hrow

end PushPuzzle.Push.AcceptanceSoundness
