/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ForwardStock

/-! Exact stationary frames for the physical two-box door interactions. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

/-- A genuine cell on the common working column at a bounded chamber row. -/
def workCell (storage : Bool) (I : Instance) (row : ℕ) (hr : row ≤ (layout storage I).depth) :
    Cell (layout storage I).width (layout storage I).height :=
  (layout storage I).point ((layout storage I).rackX - 1, row + (layout storage I).shift)
    (by dsimp; unfold Layout.width; omega)
    (by have h := (layout storage I).translated_bounds hr; dsimp; omega)

/-- A genuine working-column cell in the original ninety-row door chamber. -/
def doorCell (storage : Bool) (I : Instance) (i : Fin I.doors.length) (offset : ℕ)
    (ho : offset ≤ 90) : Cell (layout storage I).width (layout storage I).height :=
  workCell storage I (doorBase i.val + offset) (by
    change doorBase i.val + offset ≤ 90 * I.doors.length + _
    unfold doorBase
    have hi := i.isLt
    omega)

@[simp] theorem doorCell_x (storage : Bool) (I : Instance) (i : Fin I.doors.length)
    (offset : ℕ) (ho : offset ≤ 90) :
    (doorCell storage I i offset ho).1.val = (layout storage I).rackX - 1 := rfl

@[simp] theorem doorCell_y (storage : Bool) (I : Instance) (i : Fin I.doors.length)
    (offset : ℕ) (ho : offset ≤ 90) :
    (doorCell storage I i offset ho).2.val = doorBase i.val + offset + (layout storage I).shift := rfl

/-- Original door chambers have no fixed working-column boxes in their strict interiors. -/
theorem fixed_door_clear (storage : Bool) (I : Instance) (i : Fin I.doors.length)
    (p : Cell (layout storage I).width (layout storage I).height)
    (hx : p.1.val = (layout storage I).rackX - 1)
    (hlo : doorBase i.val + (layout storage I).shift < p.2.val)
    (hhi : p.2.val < doorBase i.val + (layout storage I).shift + 90) :
    (p.1.val, p.2.val) ∉ (layout storage I).fixed := by
  intro hp
  have hi := i.isLt
  have hr : 0 < (layout storage I).rackX := by unfold Layout.rackX; omega
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · have hw := (layout storage I).pins_west hp
      dsimp at hw
      omega
    · have hw := (layout storage I).rack_column hp
      dsimp at hw
      omega
  · obtain ⟨y, hy, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    have he := congrArg Prod.snd he
    dsimp at he
    rcases List.mem_append.mp hy with hd | hc
    · rcases mem_dividers storage I hd with ⟨j, _, hj⟩ | ⟨j, hj⟩
      · unfold doorBase at hlo hhi hj
        omega
      · unfold doorBase at hlo hhi
        omega
    · obtain ⟨j, hj | hj⟩ := mem_caps storage I hc
      · unfold doorBase at hlo hhi
        omega
      · have hh := chamberHeight_ge I
        unfold doorBase at hlo hhi
        omega

namespace Stock

variable {I : Instance}

/-- The selected door's stored cell, with its original finite door identity. -/
def doorPoint (storage : Bool) (S : Stock I) (i : Fin I.doors.length) :
    Cell (layout storage I).width (layout storage I).height :=
  doorCell storage I i (S.register i).row (by have := Register.row_bounds (S.register i); omega)

/-- All stationary boxes except the selected door's mobile register. -/
def roomFrame (storage : Bool) (S : Stock I) (i : Fin I.doors.length) :
    Finset (Cell (layout storage I).width (layout storage I).height) :=
  (S.stationary storage).erase (S.doorPoint storage i)

theorem roomFrame_clear (storage : Bool) (S : Stock I) (i : Fin I.doors.length)
    (p : Cell (layout storage I).width (layout storage I).height)
    (hx : p.1.val = (layout storage I).rackX - 1)
    (hlo : doorBase i.val + (layout storage I).shift < p.2.val)
    (hhi : p.2.val < doorBase i.val + (layout storage I).shift + 90) :
    p ∉ S.roomFrame storage i := by
  intro hp
  obtain ⟨hne, hp⟩ := Finset.mem_erase.mp hp
  have hp := ((layout storage I).mem_raster _ _).mp hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact fixed_door_clear storage I i p hx hlo hhi hp
  · obtain ⟨j, _, he⟩ := Finset.mem_image.mp hp
    have hy := congrArg Prod.snd he
    have hj := Register.row_bounds (S.register j)
    dsimp at hy
    have hji : j = i := by
      apply Fin.ext
      unfold doorBase at hy hlo hhi
      omega
    subst j
    apply hne
    apply Prod.ext <;> apply Fin.ext
    · exact hx
    · exact hy.symm

theorem stationary_eq_insert_doorPoint (storage : Bool) (S : Stock I) (i : Fin I.doors.length) :
    S.stationary storage = insert (S.doorPoint storage i) (S.roomFrame storage i) := by
  apply (Finset.insert_erase ?_).symm
  apply ((layout storage I).mem_raster _ _).mpr
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

end Stock
end PushPuzzle.PushPush.Doors.Source
