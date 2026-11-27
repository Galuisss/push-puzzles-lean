/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportLaneLoss
public import Push.AcceptanceProgramTrimStock
public import Push.AcceptanceSoundnessSupportPageStock
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceSoundnessCentralStock
import all Push.AcceptanceProgramLayout

/-! Real residual holes on a public column remain beyond the corridor inventory paid by its trim. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- Every hole surviving an actual public trim has physical page depth at least its paid corridor length. -/
theorem canonical_trim_retained_depth (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (side : PortLayout.Side) {a : PageColumn} (hac : a ∈ pageColumns l p side)
    (hpublic : a.privateColumn = false) (n : ℕ) (hn : (if side = .upper then 5 else 4) ≤ n)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) n) (hx : q.1.val = a.column) :
    p.Y a.level - 1 ≤ pageDepth p side q := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  let i := if side = .upper then 4 else 3
  let dir : Direction := if side = .upper then .north else .south
  let requests := ((pageColumns l p side).filter fun a => !a.privateColumn).map fun a =>
    (a.column, trimDepth p a.level)
  have hc : Scan.ClearsEmpty (instructions (emit stages T).rounds) E :=
    (program_clean_execution l p hl hM haxes initial target hr
      (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi : stages[i]? = some (.read dir requests) := by
    cases side <;> simp only [i, stages, schedule, preparation, frameSchedule, trimRound,
      dir, requests, ite_true, reduceCtorEq, ite_false, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have htake : stages.take i = trimBeforeSchedule l p target side := by
    cases side <;> simp only [i, stages, schedule, preparation, frameSchedule, trimBeforeSchedule,
      sideClearSchedule, ite_true, reduceCtorEq, ite_false, List.cons_append, List.nil_append,
      List.take_succ_cons, List.take_zero, List.append_nil, T]
  have hindex : i + 1 ≤ n := by cases side <;> simp only [i, ite_true, reduceCtorEq, ite_false] at hn ⊢ <;> omega
  have hqafter := roundResidual_antitone stages T E hc hindex hq
  have hstep := (roundResidual_step stages T E i hc hi).1
  have hbound := round_retained_reference_loss_bound dir requests _ _ _ hstep hqafter
  have hstock := trim_target_column_loss l p hl hM haxes target side hac hpublic
  have hT : (emit (stages.take i) T).remaining =
      (emit (trimBeforeSchedule l p target side) (targetHoles l p target)).remaining := by rw [htake]
  rw [hT] at hbound
  have htrim : Template.read dir requests = trimRound l p side := rfl
  rw [htrim] at hbound
  have hsame :
      ((emit (trimBeforeSchedule l p target side) T).remaining.filter fun b => b.1.val = a.column).card ≤
        ((emit [trimRound l p side] (emit (trimBeforeSchedule l p target side) T).remaining).remaining.filter
          fun b => b.1.val = a.column).card + pageDepth p side q := by
    cases side <;> simpa only [dir, pageDepth, ite_true, reduceCtorEq, ite_false, Direction.lane,
      prefixRank, Nat.add_sub_cancel, hx] using hbound
  dsimp only [T] at hsame
  omega

end PushPuzzle.Push.AcceptanceSoundness
