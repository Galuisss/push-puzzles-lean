/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.MachineStateUpdate
public import PushPush.Doors.ProtectedRows

/-! Complete-stock readout on original door chambers and private pin columns. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors

namespace Layout

theorem fixed_working_iff (L : Layout) (z : ℕ) :
    (L.rackX - 1, z) ∈ L.fixed ↔ ∃ y ∈ L.dividers ++ L.caps, z = y + L.shift := by
  have hr := L.rackX_ge
  have hpin : (L.rackX - 1, z) ∉ L.pins := by
    intro hp
    have hx := L.pins_west hp
    dsimp at hx
    omega
  have hrack : (L.rackX - 1, z) ∉ L.rack := by
    intro hp
    have hx := L.rack_column hp
    dsimp at hx
    omega
  simp only [fixed, Finset.mem_union, hpin, hrack, false_or, blockers,
    List.mem_toFinset, List.mem_map, Prod.mk.injEq, true_and]
  aesop

end Layout

namespace Source

theorem door_divider_mem (storage : Bool) (I : Instance) {i : ℕ} (hi : i < I.doors.length) :
    doorBase i ∈ (layout storage I).dividers := by
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem door_south_divider_mem (storage : Bool) (I : Instance) {i : ℕ}
    (hi : i < I.doors.length) : doorBase i + 90 ∈ (layout storage I).dividers := by
  by_cases hin : i + 1 < I.doors.length
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨i + 1, List.mem_range.mpr hin, by unfold doorBase; omega⟩
  · apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨0, List.mem_range.mpr (by omega), by dsimp; unfold doorBase; omega⟩

private theorem divider_in_door (storage : Bool) (I : Instance) {i g : ℕ}
    (hi : i < I.doors.length) (hg : g ∈ (layout storage I).dividers)
    (hlo : doorBase i ≤ g) (hhi : g ≤ doorBase i + 90) :
    g = doorBase i ∨ g = doorBase i + 90 := by
  rcases mem_dividers storage I hg with ⟨j, _, rfl⟩ | ⟨j, rfl⟩ <;>
    unfold doorBase at * <;> omega

private theorem cap_outside_door (storage : Bool) (I : Instance) {i g : ℕ}
    (hi : i < I.doors.length) (hg : g ∈ (layout storage I).caps) : doorBase i + 90 < g := by
  have hh := chamberHeight_ge I
  obtain ⟨j, he | he⟩ := mem_caps storage I hg <;> unfold doorBase <;> omega

private theorem fixed_door_column (storage : Bool) (I : Instance) {i z : ℕ}
    (hi : i < I.doors.length) (hlo : doorBase i + (layout storage I).shift ≤ z)
    (hhi : z ≤ doorBase i + (layout storage I).shift + 90) :
    ((layout storage I).rackX - 1, z) ∈ (layout storage I).fixed ↔
      z = doorBase i + (layout storage I).shift ∨
        z = doorBase i + (layout storage I).shift + 90 := by
  rw [(layout storage I).fixed_working_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rcases List.mem_append.mp hg with hg | hg
    · have hh := divider_in_door storage I hi hg (by omega) (by omega)
      omega
    · have hh := cap_outside_door storage I hi hg
      omega
  · rintro (he | he)
    · exact ⟨doorBase i, List.mem_append_left _ (door_divider_mem storage I hi), he⟩
    · exact ⟨doorBase i + 90, List.mem_append_left _ (door_south_divider_mem storage I hi),
        by omega⟩

namespace Stock

variable {I : Instance}

theorem registerPoints_column (storage : Bool) (S : Stock I) {p : ℕ × ℕ}
    (hp : p ∈ S.registerPoints storage) : p.1 = (layout storage I).rackX - 1 := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  rfl

theorem raw_column_at_pin (storage : Bool) (S : Stock I) {pin p : ℕ × ℕ}
    (hpin : pin ∈ (layout storage I).pins) (hx : p.1 = pin.1) :
    p ∈ S.rawBoxes storage ↔ p = pin ∨ p = S.signal := by
  have hwest := (layout storage I).pins_west hpin
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_union.mp hp with hp | hp
        · rcases Finset.mem_union.mp hp with hp | hp
          · exact Or.inl ((layout storage I).pins_same_column hp hpin hx)
          · have hcol := (layout storage I).rack_column hp
            omega
        · have hcol := (layout storage I).blockers_column hp
          have hr := (layout storage I).rackX_ge
          omega
      · have hcol := registerPoints_column storage S hp
        have hr := (layout storage I).rackX_ge
        omega
    · exact Or.inr (Finset.mem_singleton.mp hp)
  · rintro (rfl | rfl)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ hpin)))
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

private theorem registerPoints_in_door (storage : Bool) (S : Stock I) (i : Fin I.doors.length)
    {z : ℕ} (hlo : doorBase i.val + (layout storage I).shift ≤ z)
    (hhi : z ≤ doorBase i.val + (layout storage I).shift + 90) :
    ((layout storage I).rackX - 1, z) ∈ S.registerPoints storage ↔
      z = doorBase i.val + (S.register i).row + (layout storage I).shift := by
  constructor
  · intro hp
    obtain ⟨j, _, he⟩ := Finset.mem_image.mp hp
    have hr := Register.row_bounds (S.register j)
    have hz := congrArg Prod.snd he
    change doorBase j.val + (S.register j).row + (layout storage I).shift = z at hz
    have hji : j = i := by
      apply Fin.ext
      unfold doorBase at hlo hhi hz
      omega
    subst j
    exact hz.symm
  · intro hz
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, Prod.ext rfl hz.symm⟩

/-- Only the two dividers, that door's register and the active signal occupy its chamber. -/
theorem door_column (storage : Bool) (S : Stock I) (i : Fin I.doors.length)
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : S.Realizes storage s)
    (p : PushFS.Cell (layout storage I).width (layout storage I).height)
    (hx : p.1.val = (layout storage I).rackX - 1)
    (hlo : doorBase i.val + (layout storage I).shift ≤ p.2.val)
    (hhi : p.2.val ≤ doorBase i.val + (layout storage I).shift + 90) :
    p ∈ s.boxes ↔
      p.2.val = doorBase i.val + (layout storage I).shift ∨
      p.2.val = doorBase i.val + (layout storage I).shift + 90 ∨
      p.2.val = doorBase i.val + (S.register i).row + (layout storage I).shift ∨
      (p.1.val, p.2.val) = S.signal := by
  rw [hs]
  change p ∈ (layout storage I).raster (S.rawBoxes storage) ↔ _
  rw [(layout storage I).mem_raster]
  simp only [rawBoxes, Finset.mem_union, Finset.mem_singleton, hx]
  rw [fixed_door_column storage I i.isLt hlo hhi,
    registerPoints_in_door storage S i hlo hhi]
  tauto

end Stock
end Source
end PushPuzzle.PushPush.Doors
