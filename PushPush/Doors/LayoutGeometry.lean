/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.Layout
import Mathlib.Data.List.Enum

/-! Separation of private wire columns and the chamber rack. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Layout

open PushFS (Cell)

/-- A named physical coordinate with its rectangle bounds. -/
def point (L : Layout) (p : ℕ × ℕ) (hx : p.1 < L.width) (hy : p.2 < L.height) :
    Cell L.width L.height := (⟨p.1, hx⟩, ⟨p.2, hy⟩)

@[simp] theorem point_x (L : Layout) (p : ℕ × ℕ) (hx : p.1 < L.width) (hy : p.2 < L.height) :
    (L.point p hx hy).1.val = p.1 := rfl

@[simp] theorem point_y (L : Layout) (p : ℕ × ℕ) (hx : p.1 < L.width) (hy : p.2 < L.height) :
    (L.point p hx hy).2.val = p.2 := rfl

theorem wirePins_column_band (L : Layout) (i : ℕ) (e : Wire) {p : ℕ × ℕ}
    (hp : p ∈ L.wirePins i e) : 30 * i + 7 ≤ p.1 ∧ p.1 ≤ 30 * i + 25 := by
  simp only [wirePins, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp [wireA, wireB, wireC] <;> omega

private theorem wirePins_column_owner (L : Layout) (i j : ℕ) (e f : Wire)
    {p q : ℕ × ℕ} (hp : p ∈ L.wirePins i e) (hq : q ∈ L.wirePins j f)
    (hx : p.1 = q.1) : i = j := by
  have hp := L.wirePins_column_band i e hp
  have hq := L.wirePins_column_band j f hq
  omega

private theorem wirePins_same_column (L : Layout) (i : ℕ) (e : Wire) {p q : ℕ × ℕ}
    (hp : p ∈ L.wirePins i e) (hq : q ∈ L.wirePins i e) (hx : p.1 = q.1) : p = q := by
  simp only [wirePins, List.mem_cons, List.not_mem_nil, or_false] at hp hq
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp [wireA, wireB, wireC] at hx ⊢ <;> omega

/-- Each private pin column contains exactly one originally listed pin. -/
theorem pins_same_column (L : Layout) {p q : ℕ × ℕ}
    (hp : p ∈ L.pins) (hq : q ∈ L.pins) (hx : p.1 = q.1) : p = q := by
  obtain ⟨⟨e, i⟩, hei, hp⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hp)
  obtain ⟨⟨f, j⟩, hfj, hq⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hq)
  have hij := L.wirePins_column_owner i j e f hp hq hx
  subst j
  have hef : e = f := (List.mem_zipIdx' hei).2.trans (List.mem_zipIdx' hfj).2.symm
  subst f
  exact L.wirePins_same_column i e hp hq hx

theorem pins_west (L : Layout) {p : ℕ × ℕ} (hp : p ∈ L.pins) :
    7 ≤ p.1 ∧ p.1 + 2 < L.rackX := by
  obtain ⟨⟨e, i⟩, hei, hp⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hp)
  have hi := (List.mem_zipIdx' hei).1
  have hp := L.wirePins_column_band i e hp
  unfold rackX
  omega

theorem rack_column (L : Layout) {p : ℕ × ℕ} (hp : p ∈ L.rack) : p.1 = L.rackX := by
  simp only [rack, List.mem_toFinset, List.mem_append, List.mem_map, List.mem_flatMap] at hp
  rcases hp with ⟨y, _, rfl⟩ | ⟨y, _, hp⟩
  · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> rfl

theorem blockers_column (L : Layout) {p : ℕ × ℕ} (hp : p ∈ L.blockers) :
    p.1 = L.rackX - 1 := by
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
  rfl

private theorem fixed_west (L : Layout) {p : ℕ × ℕ} (hp : p ∈ L.fixed) : p.1 ≤ L.rackX := by
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · have := L.pins_west hp; omega
    · exact (L.rack_column hp).le
  · rw [L.blockers_column hp]
    omega

theorem initialRaw_west (L : Layout) {p : ℕ × ℕ} (hp : p ∈ L.initialRaw) :
    p.1 ≤ L.rackX := by
  rcases Finset.mem_union.mp hp with hp | hp
  · exact L.fixed_west hp
  · obtain ⟨y, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    exact Nat.sub_le _ _

theorem goalsRaw_west (L : Layout) {p : ℕ × ℕ} (hp : p ∈ L.goalsRaw) :
    p.1 ≤ L.rackX := by
  rcases Finset.mem_union.mp hp with hp | hp
  · exact L.fixed_west hp
  · obtain ⟨y, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    exact Nat.sub_le _ _

/-- The common southeast player corner is strictly east of every initial box. -/
theorem initial_player_empty (L : Layout) : L.initial.player ∉ L.initial.boxes := by
  intro hp
  have hx := L.initialRaw_west ((L.mem_raster _ _).mp hp)
  change L.width - 1 ≤ L.rackX at hx
  unfold width at hx
  omega

end PushPuzzle.PushPush.Doors.Layout
