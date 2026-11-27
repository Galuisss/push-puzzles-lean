/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.MachineState
public import PushPush.Doors.CompilerBounds
public import PushPush.Doors.ForwardSlide

/-! Player access and stationary-inventory views of complete physical door stocks. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source.Stock

open PushFS (Cell State)

variable {I : Instance}

/-- Every original register box and every structural box, without the active signal. -/
def stationary (storage : Bool) (S : Stock I) :
    Finset (Cell (layout storage I).width (layout storage I).height) :=
  (layout storage I).raster ((layout storage I).fixed ∪ S.registerPoints storage)

theorem stationary_columns (storage : Bool) (S : Stock I)
    {p : Cell (layout storage I).width (layout storage I).height} (hp : p ∈ S.stationary storage) :
    p.1.val ∈ (layout storage I).columns := by
  have hp := ((layout storage I).mem_raster _ _).mp hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (layout storage I).fixed_columns hp
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
    have hx := congrArg Prod.fst hi
    dsimp at hx
    rw [← hx]
    exact (layout storage I).working_mem_columns

theorem stationary_top (storage : Bool) (S : Stock I)
    {p : Cell (layout storage I).width (layout storage I).height}
    (hy : p.2.val = 0) : p ∉ S.stationary storage := by
  intro hp
  have hp := ((layout storage I).mem_raster _ _).mp hp
  rcases Finset.mem_union.mp hp with hp | hp
  · have hp := (layout_fits storage I).fixed_interior hp
    dsimp at hp
    omega
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
    have he := congrArg Prod.snd hi
    have hs : 0 < (layout storage I).shift := by unfold Layout.shift; omega
    dsimp at he
    omega

/-- The active signal as a genuine finite grid cell. -/
def signalCell (storage : Bool) (S : Stock I)
    (hx : S.signal.1 < (layout storage I).width) (hy : S.signal.2 < (layout storage I).height) :
    Cell (layout storage I).width (layout storage I).height :=
  (layout storage I).point S.signal hx hy

/-- All boxes are the stationary inventory plus the unique finite signal cell. -/
theorem boxes_eq_insert_signal (storage : Bool) (S : Stock I)
    (hx : S.signal.1 < (layout storage I).width) (hy : S.signal.2 < (layout storage I).height) :
    S.boxes storage = insert (S.signalCell storage hx hy) (S.stationary storage) := by
  ext p
  simp only [boxes, rawBoxes, stationary, Layout.mem_raster, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_insert]
  have he : (p.1.val, p.2.val) = S.signal ↔ p = S.signalCell storage hx hy := by
    constructor
    · intro he
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
    · intro he
      cases he
      rfl
  rw [he]
  tauto

end PushPuzzle.PushPush.Doors.Source.Stock
