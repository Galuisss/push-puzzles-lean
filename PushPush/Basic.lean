/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Slide
public import Push.Encoding

/-! Wall-free maximum sliding with a prescribed player destination. -/

@[expose] public section
namespace PushPuzzle.PushPush

/-- Dense wall-free rectangles with a starting state and player destination. -/
abbrev Instance := Push.Instance

/-- The same explicit dense input encoding as ordinary pushing. -/
abbrev encoding := Push.encoding

/-- The player reaches the destination using maximum slides. -/
def Instance.Solvable (I : Instance) : Prop :=
  ∃ t, Reachable I.initial t ∧ t.player = I.target

/-- The ordinary PushPush-* decision problem. -/
def solvable : Set Instance := {I | Instance.Solvable I}

end PushPuzzle.PushPush
