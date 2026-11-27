/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Slide
public import PushS.Encoding

/-! Wall-free maximum sliding with an exact target box set. -/

@[expose] public section
namespace PushPuzzle.PushPushS

/-- Dense wall-free rectangles with equally many initial boxes and storage targets. -/
abbrev Instance := PushS.Instance

/-- The existing explicit dense storage encoding. -/
abbrev encoding := PushS.encoding

/-- Every box reaches the exact target set; the final player is unrestricted. -/
def Instance.Solvable (I : Instance) : Prop :=
  ∃ t, PushPush.Reachable I.initial t ∧ t.boxes = I.board.goals

/-- The PushPush-*S decision problem. -/
def solvable : Set Instance := {I | Instance.Solvable I}

end PushPuzzle.PushPushS
