/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramComplete
public import PushS.PortPhysicalCompleteness

/-! A canonical target computation walks to the southeast corner and pays the complete actual reader word. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS

/-- The actual canonical target bitmap can be read at the southeast frame corner on the same board. -/
theorem canonical_forward (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial (l.cornerState p (l.canonical target)).toState) :
    ∃ t : State (p.W + 1) (p.H + 1),
      Reachable (l.canonicalInstance p hl hM haxes initial target).board none
        (l.canonicalInstance p hl hM haxes initial target).initial t ∧
      t.player.1.val + 1 = p.W + 1 ∧ t.player.2.val + 1 = p.H + 1 ∧
      Scan.Accepts (instructions (program l p target).rounds) (holes t) := by
  let I := l.canonicalInstance p hl hM haxes initial target
  let t := l.pageFrameState p (l.canonical target) .lower (Fin.last p.W)
  have hwalk := l.pageFrame_reachable p (l.canonical target) I.board I.walls_empty none .lower (Fin.last p.W)
  refine ⟨t.toState, hr.trans hwalk, rfl, rfl, ?_⟩
  have hh : holes t.toState = targetHoles l p target := by
    rw [t.holes_toState]
    rfl
  rw [hh]
  exact ⟨∅, program_accepts_target l p target⟩

end PushPuzzle.Push.AcceptanceProgram
