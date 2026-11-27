/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog
public import PushFS.StaticPlacement
public import PushFS.Gadgets.Wires.Soundness.Horizontal
public import PushFS.Gadgets.Wires.Soundness.Turn

/-! Unconditional finite-glyph instantiations of the ambient physical soundness contracts. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Soundness

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Literal source-to-target coordinate order for all four full physical slot tables. -/
theorem slots_order_x (k : Wires.Kind) : ∀ (a b : Bool) (i j : Fin k.count),
    (k.template.position a i).1.val < (k.template.position a j).1.val →
    (k.template.position b i).1.val < (k.template.position b j).1.val := by cases k <;> decide +kernel

theorem slots_order_y (k : Wires.Kind) : ∀ (a b : Bool) (i j : Fin k.count),
    (k.template.position a i).2.val < (k.template.position a j).2.val →
    (k.template.position b i).2.val < (k.template.position b j).2.val := by cases k <;> decide +kernel

namespace HorizontalKind

end HorizontalKind

end PushPuzzle.PushFS.Gadgets.Wires.Soundness
