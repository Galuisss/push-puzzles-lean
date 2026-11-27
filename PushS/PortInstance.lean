/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortInventorySum
public import PushS.Boundary

/-!
# Actual wall-free instances emitted by valid two-page port layouts

The player, rectangle and equal inventories are proved for the actual complete recipe.
The canonical instance uses the same dense emitter and standard polynomial-time encoding.

## Main results

* `canonicalInstance`: the actual complete wall-free storage instance.
* `computableInPolyTime_canonicalInstance_of_layout`: standard PT with the actual layout properties.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open _root_.Turing.MultiTapeTM

/-- The genuine complete marked instance for two physical signal states. -/
@[expose] def physicalInstance (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState) : Instance :=
  (l.segmentRecipe p initial target).toInstance (l.segmentRecipe_valid p hl hM ha initial target)

/-- The genuine complete marked instance for two interface bit arrays. -/
@[expose] def canonicalInstance (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : List Bool) : Instance :=
  (l.canonicalRecipe p initial target).toInstance (l.canonicalRecipe_valid p hl hM ha initial target)

/-- The constructed physical instance has exactly the emitted initial hole set. -/
theorem physicalInstance_initial_holes (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState) :
    PushS.holes (l.physicalInstance p hl hM ha initial target).initial =
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial) := by
  change (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial))ᶜᶜ = _
  simp

/-- The complement of the actual storage goals is the emitted target hole set. -/
theorem physicalInstance_goal_holes (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState) :
    (l.physicalInstance p hl hM ha initial target).board.goalsᶜ =
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target) := by
  change (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target))ᶜᶜ = _
  simp

/-- The actual initial player lies at the empty frame corner. -/
theorem physicalInstance_initial_frame (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState) :
    (l.physicalInstance p hl hM ha initial target).initial.player ∈ Boundary.frame := by
  apply (Boundary.mem_frame _).mpr
  exact ⟨.north, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

/-- The constructed physical instance has exactly the raw dense data emitted by its recipe. -/
theorem physicalInstance_data_eq (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState) :
    PushFS.Encoding.data (l.physicalInstance p hl hM ha initial target).toInstance =
      (l.segmentRecipe p initial target).emit :=
  (l.segmentRecipe p initial target).data_eq _

/-- The constructed canonical instance has the actual emitted fixed and signal bitmap. -/
theorem canonicalInstance_data_eq (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : List Bool) :
    PushFS.Encoding.data (l.canonicalInstance p hl hM ha initial target).toInstance =
      (l.canonicalRecipe p initial target).emit :=
  (l.canonicalRecipe p initial target).data_eq _

/-- The actual canonical instance is polynomial-time in the standard encoding. The fixed
working-level family and the actual source layout properties supply all constructor proofs. -/
theorem computableInPolyTime_canonicalInstance_of_layout {α : Type} {enc : α ↪ List Bool}
    {layout : α → PortLayout} {p : α → Scales.Parameters} {M : ℕ}
    (hl : ComputableInPolyTime layout enc encPortLayout)
    (haxes : ComputableInPolyTime (fun a => (p a).axes) enc encUnary)
    (hlevels : ∀ a, (p a).levels = M)
    (hpages : ∀ a, (layout a).pages.Valid)
    (hM : ∀ a, (layout a).pages.highest ≤ (p a).levels)
    (ha : ∀ a, (layout a).portCount ≤ (p a).axes)
    {initial target : α → List Bool}
    (hi : ComputableInPolyTime initial enc (encList encBool))
    (ht : ComputableInPolyTime target enc (encList encBool)) :
    ComputableInPolyTime
      (fun a => (layout a).canonicalInstance (p a) (hpages a) (hM a) (ha a) (initial a) (target a))
      enc encoding :=
  computableInPolyTime_canonicalInstance hl haxes hlevels hi ht
    (fun a => (layout a).canonicalRecipe_valid (p a) (hpages a) (hM a) (ha a) (initial a) (target a))

end PushPuzzle.PushS.PortLayout
