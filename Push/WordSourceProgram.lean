/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.WordSourceBoard
public import Push.AcceptanceProgramPolyTime
public import Push.AcceptanceProgramSkeleton
import all Push.AcceptanceProgram

/-! Standard emission of the actual repaired H-word source's complete compact acceptance program. -/

public section
namespace PushPuzzle.Push.WordSource

open PushFS PushS Cslib.Complexity Turing.MultiTapeTM AcceptanceProgram

attribute [local irreducible] PushPuzzle.NCL.HWord.Strip.Sweep.compile
  Partner.Cuts.repair Partner.Cuts.repairAxes

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- All actual compact read requests and clear-lane sets emit in standard polynomial time from the original H-word. -/
theorem program_rounds_polyTime :
    ComputableInPolyTime (fun x =>
      (program (layout H hq x) (scales H hq x) (targetAxes H hq x)).rounds)
      (NCL.HWord.encInstance q) encRounds :=
  AcceptanceProgram.program_rounds_polyTime
    (computableInPolyTime_layout H hq) (computableInPolyTime_scales_axes H hq)
    (fun _ => rfl) (computableInPolyTime_targetAxes H hq)
    (layout_valid H hq) (highest_le_scales_levels H hq)

/-- The actual H-word acceptance family has one fixed read/clear side skeleton at its fixed level allocation. -/
theorem program_shapes (x : NCL.HWord.Instance q) :
    (program (layout H hq x) (scales H hq x) (targetAxes H hq x)).rounds.map Round.shape =
      skeleton (levelBudget q + 1) :=
  AcceptanceProgram.program_shapes _ _ _

end PushPuzzle.Push.WordSource
