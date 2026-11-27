/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Soundness.Pair
public import PushFS.Gadgets.Wires.Soundness.Corner
public import PushFS.Gadgets.Wires.Turn

/-! Static arm geometry of the full guarded turn. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Soundness

namespace TurnGeometry

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- All positions of the same arm are joined through the real floor table. -/
theorem slots_component (phase : Bool) (i j : Fin 29)
    (harm : (i.val < 14 ∧ j.val < 14) ∨ (14 ≤ i.val ∧ 14 ≤ j.val)) :
    SameComponent (Turn.template.board ∅) (Turn.template.position phase i) (Turn.template.position phase j) := by
  have check : ∀ (phase : Bool) (i j : Fin 29),
      ((i.val < 14 ∧ j.val < 14) ∨ (14 ≤ i.val ∧ 14 ≤ j.val)) →
      Gates.staticRun Turn.template.wall (Turn.template.position phase i)
        (Template.slotDirections (Turn.template.position phase i) (Turn.template.position phase j)) =
          some (Turn.template.position phase j) := by decide +kernel
  exact ⟨Gates.staticRun_sound (Turn.template.wall_correct ∅) (check phase i j harm),
    Gates.staticRun_sound (Turn.template.wall_correct ∅) (check phase j i (harm.elim (Or.inl ∘ And.symm) (Or.inr ∘ And.symm)))⟩

/-- Both literal flip intervals have their exact protective wall cells. -/
theorem strip31 : StripWalls (Turn.template.board ∅) 31 31 9 := by
  refine ⟨?_,?_⟩ <;> decide +kernel
theorem strip34 : StripWalls (Turn.template.board ∅) 34 34 9 := by
  refine ⟨?_,?_⟩ <;> decide +kernel

theorem flip_normal : ∀ phase : Bool,
    ((Turn.template.position phase 4).1.val+1 < 31 ∨ 32 < (Turn.template.position phase 3).1.val) ∧
    ((Turn.template.position phase 3).1.val+1 < 34 ∨ 35 < (Turn.template.position phase 2).1.val) := by decide +kernel

theorem corner_normal : ∀ phase : Bool,
    11 < (Turn.template.position phase 13).1.val ∨ 10 < (Turn.template.position phase 14).2.val := by decide +kernel

theorem arms : ∀ (phase : Bool) (i : Fin 29),
    (i.val < 14 → (Turn.template.position phase i).2.val = 9 ∧ 10 < (Turn.template.position phase i).1.val) ∧
    (14 ≤ i.val → (Turn.template.position phase i).1.val = 10 ∧ 9 < (Turn.template.position phase i).2.val) := by
  decide +kernel

theorem horizontal_order : ∀ (phase : Bool) (i j : Fin 29), i < j → j.val < 14 →
    (Turn.template.position phase j).1.val < (Turn.template.position phase i).1.val := by decide +kernel

theorem vertical_order : ∀ (phase : Bool) (i j : Fin 29), 14 ≤ i.val → i < j →
    (Turn.template.position phase i).2.val < (Turn.template.position phase j).2.val := by decide +kernel

end TurnGeometry

end PushPuzzle.PushFS.Gadgets.Wires.Soundness
