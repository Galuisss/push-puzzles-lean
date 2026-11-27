/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.WordSourceBoard
public import Push.SourceGame
public import Push.AcceptanceProgramForward
public import PushFS.WallCongruence

/-! The actual marked hard source as an ordinary southeast-target game with its complete acceptance program. -/

@[expose] public section
namespace PushPuzzle.Push.WordSource

open PushFS PushS Cslib.Complexity Turing.MultiTapeTM

attribute [local irreducible] PushPuzzle.NCL.HWord.Strip.Sweep.compile
  Partner.Cuts.repair Partner.Cuts.repairAxes

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- Retain the complete repaired source bitmap and require the southeast frame corner. -/
def sourceGame (x : NCL.HWord.Instance q) : Push.Instance := SourceGame.ofStorage (puzzle H hq x)

/-- The complete compact read/clear word emitted from the actual repaired canonical target. -/
def rounds (x : NCL.HWord.Instance q) : List AcceptanceProgram.Round :=
  (AcceptanceProgram.program (layout H hq x) (scales H hq x) (targetAxes H hq x)).rounds

/-- One actual source computation reaches the frame corner with a bitmap accepted by the complete emitted word. -/
def accepted (x : NCL.HWord.Instance q) : Prop :=
  ∃ t : State (sourceGame H hq x).width (sourceGame H hq x).height,
    Reachable (sourceGame H hq x).board none (sourceGame H hq x).initial t ∧
      t.player = (sourceGame H hq x).target ∧
        Scan.Accepts (AcceptanceProgram.instructions (rounds H hq x)) (holes t)

/-- A real accepted source computation is also a computation of the same original canonical marked board. -/
theorem accepted_physical {x : NCL.HWord.Instance q} (ha : accepted H hq x) :
    ∃ t : State ((scales H hq x).W + 1) ((scales H hq x).H + 1),
      Reachable (puzzle H hq x).board none (puzzle H hq x).initial t ∧
        Scan.Accepts (AcceptanceProgram.instructions (rounds H hq x)) (holes t) := by
  obtain ⟨t, ht, _, ha⟩ := ha
  exact ⟨t, ht.reboard (SourceGame.ofStorage_walls (puzzle H hq x)), ha⟩

/-- Every positive source word has a complete real source computation paying the entire acceptance word. -/
theorem accepted_of_mem {x : NCL.HWord.Instance q} (hx : x ∈ NCL.HWord.language H) : accepted H hq x := by
  obtain ⟨t, hr, hx, hy, ha⟩ := AcceptanceProgram.canonical_forward
    (layout H hq x) (scales H hq x) (layout_valid H hq x) (highest_le_scales_levels H hq x)
    (portCount_le_scales_axes H hq x) (initialAxes H hq x) (targetAxes H hq x) (puzzle_forward H hq hx)
  refine ⟨t, hr.reboard (SourceGame.ofStorage_walls (puzzle H hq x)).symm, ?_, ha⟩
  obtain ⟨htx, hty⟩ := SourceGame.ofStorage_target (puzzle H hq x)
  apply Prod.ext <;> apply Fin.ext
  · change t.player.1.val = (sourceGame H hq x).target.1.val
    change t.player.1.val + 1 = (puzzle H hq x).width at hx
    change (sourceGame H hq x).target.1.val + 1 = (puzzle H hq x).width at htx
    omega
  · change t.player.2.val = (sourceGame H hq x).target.2.val
    change t.player.2.val + 1 = (puzzle H hq x).height at hy
    change (sourceGame H hq x).target.2.val + 1 = (puzzle H hq x).height at hty
    omega

end PushPuzzle.Push.WordSource
