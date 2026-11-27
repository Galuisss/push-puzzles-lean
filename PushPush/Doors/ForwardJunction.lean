/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ForwardRooms

/-! Clear working-column corridors inside the regular location and choice rooms. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell)

private theorem scaled_outside {r a b offset : ℕ} (hr : 4 ≤ r) (ho : offset < r)
    (hedge : offset ≤ 2 ∨ r - 2 ≤ offset) :
    ¬(r * a + 2 < r * b + offset ∧ r * b + offset < r * a + r - 2) := by
  intro h
  by_cases he : a = b
  · subst b
    omega
  · rcases Nat.lt_or_gt_of_ne he with hl | hl
    · have hm : r * a + r ≤ r * b := by
        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left r (Nat.succ_le_of_lt hl)
      omega
    · have hm : r * b + r ≤ r * a := by
        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left r (Nat.succ_le_of_lt hl)
      omega

/-- A genuine working-column cell in a regular junction chamber. -/
def roomCell (storage : Bool) (I : Instance) (v j offset : ℕ)
    (hv : v < (labels I).length) (hj : j < slots I) (ho : offset < chamberHeight I) :
    Cell (layout storage I).width (layout storage I).height :=
  workCell storage I (roomBase I v j + offset) (room_row_fit storage I hv hj ho)

@[simp] theorem roomCell_x (storage : Bool) (I : Instance) (v j offset : ℕ)
    (hv : v < (labels I).length) (hj : j < slots I) (ho : offset < chamberHeight I) :
    (roomCell storage I v j offset hv hj ho).1.val = (layout storage I).rackX - 1 := rfl

@[simp] theorem roomCell_y (storage : Bool) (I : Instance) (v j offset : ℕ)
    (hv : v < (labels I).length) (hj : j < slots I) (ho : offset < chamberHeight I) :
    (roomCell storage I v j offset hv hj ho).2.val = roomBase I v j + offset + (layout storage I).shift := rfl

/-- Strictly between the two possible endpoint caps, the junction working column is empty. -/
private theorem fixed_junction_clear (storage : Bool) (I : Instance) (v j : ℕ)
    (p : Cell (layout storage I).width (layout storage I).height)
    (hx : p.1.val = (layout storage I).rackX - 1)
    (hlo : roomBase I v j + (layout storage I).shift + 2 < p.2.val)
    (hhi : p.2.val < roomBase I v j + (layout storage I).shift + chamberHeight I - 2) :
    (p.1.val, p.2.val) ∉ (layout storage I).fixed := by
  intro hp
  have hr : 0 < (layout storage I).rackX := by unfold Layout.rackX; omega
  have hh := chamberHeight_ge I
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
    · rcases mem_dividers storage I hd with ⟨k, hk, hy⟩ | ⟨k, hy⟩
      · dsimp [roomBase, doorBase] at hlo hy
        omega
      · have hc := scaled_outside (by omega : 4 ≤ chamberHeight I)
          (by omega : 0 < chamberHeight I) (Or.inl (by omega : 0 ≤ 2))
          (a := slots I * v + j) (b := k)
        apply hc
        unfold roomBase at hlo hhi
        omega
    · obtain ⟨k, hy | hy⟩ := mem_caps storage I hc
      · have hc := scaled_outside (by omega : 4 ≤ chamberHeight I)
          (by omega : 2 < chamberHeight I) (Or.inl (by omega : 2 ≤ 2))
          (a := slots I * v + j) (b := k)
        apply hc
        unfold roomBase at hlo hhi
        omega
      · have hc := scaled_outside (by omega : 4 ≤ chamberHeight I)
          (by omega : chamberHeight I - 2 < chamberHeight I) (Or.inr le_rfl)
          (a := slots I * v + j) (b := k)
        apply hc
        unfold roomBase at hlo hhi
        omega

namespace Stock

variable {I : Instance}

theorem stationary_junction_clear (storage : Bool) (S : Stock I) (v j : ℕ)
    (p : Cell (layout storage I).width (layout storage I).height)
    (hx : p.1.val = (layout storage I).rackX - 1)
    (hlo : roomBase I v j + (layout storage I).shift + 2 < p.2.val)
    (hhi : p.2.val < roomBase I v j + (layout storage I).shift + chamberHeight I - 2) :
    p ∉ S.stationary storage := by
  intro hp
  have hp := ((layout storage I).mem_raster _ _).mp hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact fixed_junction_clear storage I v j p hx hlo hhi hp
  · obtain ⟨k, _, he⟩ := Finset.mem_image.mp hp
    have hy := congrArg Prod.snd he
    have hk := k.isLt
    have hrow := Register.row_bounds (S.register k)
    dsimp at hy
    dsimp [roomBase, doorBase] at hlo hy
    omega

end Stock
end PushPuzzle.PushPush.Doors.Source
