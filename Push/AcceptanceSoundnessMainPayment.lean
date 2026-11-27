/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramMainStock
public import Push.AcceptanceAxisNoExport
public import Push.AcceptanceSoundnessWireBalanced
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all PushFS.Grid

/-! The two real main-axis reads pay four distinct ordinary-axis holes and bound the remaining one-way surplus. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

/-- Every genuine main read pays exactly two actual holes on its endpoint's physical column. -/
theorem canonical_main_column_loss (e : Endpoint) (he : e ∈ l.endpoints)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    let stages := schedule l p (targetHoles l p target \ Boundary.frame).card
    let T := targetHoles l p target
    let i := if e.side = .upper then 6 else 7
    ((roundResidual stages T (PushS.holes t) (i + 1)).filter fun q => q.1.val = p.x e.port).card + 2 =
      ((roundResidual stages T (PushS.holes t) i).filter fun q => q.1.val = p.x e.port).card := by
  let T := targetHoles l p target
  let stages := schedule l p (T \ Boundary.frame).card
  let i := if e.side = .upper then 6 else 7
  let dir : Direction := if e.side = .upper then .north else .south
  let requests := (l.endpoints.filter fun f => f.side == e.side).map fun f => (p.x f.port, p.Y f.level + 2)
  let R := (emit (stages.take i) T).remaining
  let A := roundResidual stages T (PushS.holes t) i
  let F := roundResidual stages T (PushS.holes t) (i + 1)
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi : stages[i]? = some (.read dir requests) := by
    cases hs : e.side <;> simp only [i, stages, schedule, preparation, frameSchedule, mainTop, mainBottom,
      dir, requests, hs, ite_true, reduceCtorEq, ite_false, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hread := (roundResidual_step stages T (PushS.holes t) i hc hi).1
  have hloss : (A.filter fun q => q.1.val = p.x e.port).card +
      ((emit [.read dir requests] R).remaining.filter fun q => q.1.val = p.x e.port).card =
      (F.filter fun q => q.1.val = p.x e.port).card + (R.filter fun q => q.1.val = p.x e.port).card := by
    have hh := round_reference_lane_loss dir requests R A F (p.x e.port) hread
    cases hs : e.side <;> simpa only [dir, Direction.lane, hs, ite_true, reduceCtorEq, ite_false] using hh
  have href := main_target_column_loss l p hl hM haxes target e he
  change ((emit [mainRound l p e.side] R).remaining.filter fun q => q.1.val = p.x e.port).card + 2 =
    (R.filter fun q => q.1.val = p.x e.port).card at href
  have hemit : mainRound l p e.side = .read dir requests := by
    cases hs : e.side <;> simp only [mainRound, dir, requests, hs,
      ite_true, reduceCtorEq, ite_false]
  rw [hemit] at href
  change (F.filter fun q => q.1.val = p.x e.port).card + 2 = (A.filter fun q => q.1.val = p.x e.port).card
  omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
