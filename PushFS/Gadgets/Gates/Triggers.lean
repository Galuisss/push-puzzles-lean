/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Slots
public import PushFS.Gadgets.OR

/-! Physical trigger identities and their connection to the gate soundness thresholds. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Gates


-- The dependent indices refer to the explicitly listed complete physical slot array.
set_option maxRecDepth 65536

/-- The left trigger is physical identity 1 in either gate. -/
def triggerA (kind : Bool) : Fin (slots kind).length :=
  ⟨1, by rw [slots_length]; cases kind <;> decide⟩

/-- The upper trigger is physical identity 2 in either gate. -/
def triggerB (kind : Bool) : Fin (slots kind).length :=
  ⟨2, by rw [slots_length]; cases kind <;> decide⟩

/-- The output trigger is physical identity 4 in either gate. -/
def triggerC (kind : Bool) : Fin (slots kind).length :=
  ⟨4, by rw [slots_length]; cases kind <;> decide⟩

theorem position_triggerA (kind : Bool) (b : Signals) :
    position kind b (triggerA kind) = if b.left then (42, 90) else (43, 90) := by
  cases kind <;> rfl

theorem position_triggerB (kind : Bool) (b : Signals) :
    position kind b (triggerB kind) =
      if kind then (if b.upper then (43, 88) else (43, 89))
      else (if b.upper then (44, 88) else (44, 89)) := by
  cases kind <;> rfl

theorem position_triggerC (kind : Bool) (b : Signals) :
    position kind b (triggerC kind) =
      if kind then (if b.right then (46, 90) else (47, 90))
      else (if b.right then (47, 90) else (48, 90)) := by
  cases kind <;> rfl

/-- The three trigger identities in the same complete canonical player/box state. -/
def configuration (kind : Bool) (b : Signals) : AND.Configuration 81 107 :=
  (labelled kind b).triple (triggerA kind) (triggerB kind) (triggerC kind)

/-- The canonical AND flags have exactly the existing geometric threshold meaning. -/
theorem legal_iff_and_good (b : Signals) : legal true b ↔ AND.Good 43 90 (configuration true b) := by
  unfold AND.Good
  rcases b with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide +kernel

/-- The canonical OR flags have exactly the existing geometric threshold meaning. -/
theorem legal_iff_or_good (b : Signals) : legal false b ↔ OR.Good 44 90 (configuration false b) := by
  unfold OR.Good
  rcases b with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide +kernel

end PushPuzzle.PushFS.Gadgets.Gates
