/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.StockGeometry
public import PushPush.Doors.WireSourceRows
public import PushPush.Doors.ForwardStock

/-! Complete working-column inventory of every regular location and choice chamber. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

private theorem inner_address {base stride a b offset : ℕ}
    (ho : 0 < offset) (hu : offset < stride)
    (hlo : base + stride * a ≤ base + stride * b + offset)
    (hhi : base + stride * b + offset ≤ base + stride * a + stride) : a = b := by
  by_contra he
  rcases Nat.lt_or_gt_of_ne he with hl | hl
  · have hm : stride * a + stride ≤ stride * b := by
      simpa only [Nat.mul_succ] using Nat.mul_le_mul_left stride (Nat.succ_le_of_lt hl)
    omega
  · have hm : stride * b + stride ≤ stride * a := by
      simpa only [Nat.mul_succ] using Nat.mul_le_mul_left stride (Nat.succ_le_of_lt hl)
    omega

private theorem divider_address {base stride a b : ℕ} (hr : 0 < stride)
    (hlo : base + stride * a ≤ base + stride * b)
    (hhi : base + stride * b ≤ base + stride * a + stride) : b = a ∨ b = a + 1 := by
  by_cases he : b = a
  · exact Or.inl he
  · have hab : a < b := by
      by_contra h
      have hb : b < a := by omega
      have hm : stride * b + stride ≤ stride * a := by
        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left stride (Nat.succ_le_of_lt hb)
      omega
    have hle : b ≤ a + 1 := by
      by_contra hb
      have hm : stride * a + stride + stride ≤ stride * b := by
        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left stride (show a + 1 + 1 ≤ b by omega)
      omega
    exact Or.inr (by omega)

theorem junction_divider_mem (storage : Bool) (I : Instance) (v j : ℕ)
    (hv : v < (labels I).length) (hj : j < slots I) :
    roomBase I v j ∈ (layout storage I).dividers := by
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨slots I * v + j, List.mem_range.mpr ?_, rfl⟩
  have := room_index_lt I hv hj
  omega

theorem junction_south_divider_mem (storage : Bool) (I : Instance) (v j : ℕ)
    (hv : v < (labels I).length) (hj : j < slots I) :
    roomBase I v j + chamberHeight I ∈ (layout storage I).dividers := by
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨slots I * v + j + 1, List.mem_range.mpr ?_, ?_⟩
  · have := room_index_lt I hv hj
    omega
  · simp [roomBase, Nat.mul_add, Nat.add_assoc]

private theorem junction_dividers_iff (storage : Bool) (I : Instance) (v j z : ℕ)
    (hv : v < (labels I).length) (hj : j < slots I)
    (hlo : roomBase I v j ≤ z) (hhi : z ≤ roomBase I v j + chamberHeight I) :
    z ∈ (layout storage I).dividers ↔ z = roomBase I v j ∨ z = roomBase I v j + chamberHeight I := by
  constructor
  · intro hz
    rcases mem_dividers storage I hz with ⟨i, hi, he⟩ | ⟨k, he⟩
    · dsimp [roomBase, doorBase] at hlo he
      omega
    · have hh := chamberHeight_ge I
      have hd := divider_address (by omega : 0 < chamberHeight I)
        (base := 90 * I.doors.length) (a := slots I * v + j) (b := k)
        (by unfold roomBase at hlo; omega) (by unfold roomBase at hhi; omega)
      rcases hd with rfl | rfl
      · exact Or.inl he
      · apply Or.inr
        simpa [roomBase, Nat.mul_add, Nat.add_assoc] using he
  · rintro (rfl | rfl)
    · exact junction_divider_mem storage I v j hv hj
    · exact junction_south_divider_mem storage I v j hv hj

private theorem junction_caps_iff (storage : Bool) (I : Instance) (v j z : ℕ)
    (hv : v < (labels I).length) (hj : j < slots I)
    (hlo : roomBase I v j ≤ z) (hhi : z ≤ roomBase I v j + chamberHeight I) :
    z ∈ (layout storage I).caps ↔
      (upperUsed I v j = true ∧ z = roomBase I v j + 2) ∨
      (lowerUsed I v j = true ∧ z = roomBase I v j + chamberHeight I - 2) := by
  have hh := chamberHeight_ge I
  constructor
  · intro hz
    obtain ⟨v', hv', hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨j', hj', hz⟩ := List.mem_flatMap.mp hz
    have hj' := List.mem_range.mp hj'
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at hz
    rcases hz with ⟨hused, he⟩ | ⟨hused, he⟩
    · have ha := inner_address (by omega : 0 < 2) (by omega : 2 < chamberHeight I)
        (base := 90 * I.doors.length) (a := slots I * v + j) (b := slots I * v' + j')
        (by dsimp [roomBase] at he hlo; omega) (by dsimp [roomBase] at he hhi; omega)
      obtain ⟨hvv, hjj⟩ := row_address_injective hj hj' ha
      subst v'
      subst j'
      exact Or.inl ⟨hused, he⟩
    · have ha := inner_address (by omega : 0 < chamberHeight I - 2)
        (by omega : chamberHeight I - 2 < chamberHeight I)
        (base := 90 * I.doors.length) (a := slots I * v + j) (b := slots I * v' + j')
        (by dsimp [roomBase] at he hlo; omega) (by dsimp [roomBase] at he hhi; omega)
      obtain ⟨hvv, hjj⟩ := row_address_injective hj hj' ha
      subst v'
      subst j'
      exact Or.inr ⟨hused, he⟩
  · intro hz
    apply List.mem_flatMap.mpr
    refine ⟨v, List.mem_range.mpr hv, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨j, List.mem_range.mpr hj, ?_⟩
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton]
    exact hz

theorem junction_upper_cap_iff (storage : Bool) (I : Instance) (v j : ℕ)
    (hv : v < (labels I).length) (hj : j < slots I) :
    roomBase I v j + 2 ∈ (layout storage I).caps ↔ upperUsed I v j = true := by
  have hh := chamberHeight_ge I
  rw [junction_caps_iff storage I v j _ hv hj (by omega) (by omega)]
  have hne : roomBase I v j + 2 ≠ roomBase I v j + chamberHeight I - 2 := by omega
  simp [hne]

theorem junction_lower_cap_iff (storage : Bool) (I : Instance) (v j : ℕ)
    (hv : v < (labels I).length) (hj : j < slots I) :
    roomBase I v j + chamberHeight I - 2 ∈ (layout storage I).caps ↔ lowerUsed I v j = true := by
  have hh := chamberHeight_ge I
  rw [junction_caps_iff storage I v j _ hv hj (by omega) (by omega)]
  have hne : roomBase I v j + chamberHeight I - 2 ≠ roomBase I v j + 2 := by omega
  simp [hne]

namespace Stock

variable {I : Instance}

/-- Complete stationary inventory in the closed junction chamber. -/
theorem stationary_junction_column (storage : Bool) (S : Stock I) (v j : ℕ)
    (hv : v < (labels I).length) (hj : j < slots I)
    (p : PushFS.Cell (layout storage I).width (layout storage I).height)
    (hx : p.1.val = (layout storage I).rackX - 1)
    (hlo : roomBase I v j + (layout storage I).shift ≤ p.2.val)
    (hhi : p.2.val ≤ roomBase I v j + (layout storage I).shift + chamberHeight I) :
    p ∈ S.stationary storage ↔
      p.2.val = roomBase I v j + (layout storage I).shift ∨
      p.2.val = roomBase I v j + (layout storage I).shift + chamberHeight I ∨
      (upperUsed I v j = true ∧ p.2.val = roomBase I v j + 2 + (layout storage I).shift) ∨
      (lowerUsed I v j = true ∧ p.2.val = roomBase I v j + chamberHeight I - 2 + (layout storage I).shift) := by
  have hh := chamberHeight_ge I
  have hreg : (p.1.val, p.2.val) ∉ S.registerPoints storage := by
    intro hp
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hp
    have hy := congrArg Prod.snd he
    have hi := i.isLt
    have hr := Register.row_bounds (S.register i)
    dsimp [doorBase] at hy
    unfold roomBase at hlo
    omega
  rw [stationary, (layout storage I).mem_raster]
  simp only [Finset.mem_union, hreg, or_false]
  rw [hx, (layout storage I).fixed_working_iff]
  constructor
  · rintro ⟨z, hz, he⟩
    have hzlo : roomBase I v j ≤ z := by omega
    have hzhi : z ≤ roomBase I v j + chamberHeight I := by omega
    rcases List.mem_append.mp hz with hz | hz
    · have hd := (junction_dividers_iff storage I v j z hv hj hzlo hzhi).mp hz
      omega
    · have hc := (junction_caps_iff storage I v j z hv hj hzlo hzhi).mp hz
      rcases hc with ⟨hu, rfl⟩ | ⟨hl, rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨hu, he⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hl, he⟩))
  · intro hp
    rcases hp with hp | hp | ⟨hu, hp⟩ | ⟨hl, hp⟩
    · exact ⟨roomBase I v j, List.mem_append_left _ (junction_divider_mem storage I v j hv hj), hp⟩
    · exact ⟨roomBase I v j + chamberHeight I,
        List.mem_append_left _ (junction_south_divider_mem storage I v j hv hj), by omega⟩
    · exact ⟨roomBase I v j + 2,
        List.mem_append_right _ ((junction_upper_cap_iff storage I v j hv hj).mpr hu), hp⟩
    · exact ⟨roomBase I v j + chamberHeight I - 2,
        List.mem_append_right _ ((junction_lower_cap_iff storage I v j hv hj).mpr hl), hp⟩

end Stock
end PushPuzzle.PushPush.Doors.Source
