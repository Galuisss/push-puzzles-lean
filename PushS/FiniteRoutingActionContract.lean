/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionTerminal

/-! Complete routing execution and exact owned/shared inventories on the actual strict action footprint. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Action
open PushFS

/-- Execute every physical atom, preparing the owned last interface when requested. -/
private theorem program_low_high (w : ℕ) (hw : 2 ≤ w) (length : ℕ) (switch above last : Bool) :
    Reachable (macroBoard (last:=last) w (program w length switch) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw (ownedCount w (program w length switch)+if last then 1 else 0) (program w length switch)⟩
      ⟨outerHub w _, cutBoxes w hw 1 (program w length switch)⟩ := by
  cases last
  · exact program_prepared_low_high w hw length switch above
  · exact (Terminal.program_prepare w hw length switch above false).trans
      (program_prepared_low_high w hw length switch above)

private theorem program_high_low (w : ℕ) (hw : 2 ≤ w) (length : ℕ) (switch above last : Bool) :
    Reachable (macroBoard (last:=last) w (program w length switch) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw 1 (program w length switch)⟩
      ⟨outerHub w _, cutBoxes w hw (ownedCount w (program w length switch)+if last then 1 else 0) (program w length switch)⟩ := by
  cases last
  · exact program_prepared_high_low w hw length switch above
  · exact (program_prepared_high_low w hw length switch above).trans
      (Terminal.program_prepare w hw length switch above true)

theorem program_low_high_placed (w : ℕ) (hw : 2 ≤ w) (length : ℕ) (switch above last : Bool)
    {W H : ℕ} (e : GridEmbedding (width w (program w length switch)) (height w) W H)
    {B : Board W H} {fixed : Finset (Cell W H)}
    (frame : FiniteWireFrame.Frame (active w (program w length switch) above last) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨outerHub w _, cutBoxes w hw (ownedCount w (program w length switch)+if last then 1 else 0) (program w length switch)⟩)
      (e.extend fixed ⟨outerHub w _, cutBoxes w hw 1 (program w length switch)⟩) :=
  frame.replay (program_low_high w hw length switch above last)

theorem program_high_low_placed (w : ℕ) (hw : 2 ≤ w) (length : ℕ) (switch above last : Bool)
    {W H : ℕ} (e : GridEmbedding (width w (program w length switch)) (height w) W H)
    {B : Board W H} {fixed : Finset (Cell W H)}
    (frame : FiniteWireFrame.Frame (active w (program w length switch) above last) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨outerHub w _, cutBoxes w hw 1 (program w length switch)⟩)
      (e.extend fixed ⟨outerHub w _, cutBoxes w hw (ownedCount w (program w length switch)+if last then 1 else 0) (program w length switch)⟩) :=
  frame.replay (program_high_low w hw length switch above last)

end PushPuzzle.PushS.FiniteRouting.Line.Action
