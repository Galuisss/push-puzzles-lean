/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Gadgets.Wires.Catalog.Data
import Mathlib.Data.Fintype.Pi

/-! The actual catalog player position is independent of both canonical endpoint phases. -/
@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private instance (k : Kind) (a b c d : Bool) :
    Decidable (@Eq Cell (puzzle k a b).initial.player (puzzle k c d).initial.player) :=
  (inferInstance : DecidableEq Cell) _ _

theorem player_same (k : Kind) (a b c d : Bool) : @Eq Cell (puzzle k a b).initial.player (puzzle k c d).initial.player := by
  have checked : ∀(k : Kind) (a b c d : Bool),@Eq Cell (puzzle k a b).initial.player (puzzle k c d).initial.player := by
    decide +kernel
  exact checked k a b c d

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
