/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.LayoutGeometry
import Mathlib.Data.List.Enum

/-! Every listed box and wire turn stays strictly inside the physical rectangle. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Layout

/-- All logical room rows lie in the declared chamber stack. -/
structure Fits (L : Layout) : Prop where
  /-- Rack input rows fit. -/
  rack : ∀ y ∈ L.rackRows, y ≤ L.depth
  /-- Divider rows fit. -/
  dividers : ∀ y ∈ L.dividers, y ≤ L.depth
  /-- Endpoint-cap rows fit. -/
  caps : ∀ y ∈ L.caps, y ≤ L.depth
  /-- Initial door storage rows fit. -/
  dataRows : ∀ y ∈ L.dataRows, y ≤ L.depth
  /-- Final door storage rows fit. -/
  goalRows : ∀ y ∈ L.goalRows, y ≤ L.depth
  /-- The initial signal row fits. -/
  launch : L.launch ≤ L.depth
  /-- The final signal row fits. -/
  stop : L.stop ≤ L.depth
  /-- Both endpoints of every actual wire fit. -/
  wires : ∀ e ∈ L.wires, e.source ≤ L.depth ∧ e.target ≤ L.depth

private theorem level_bounds (L : Layout) {i : ℕ} (hi : i < 2 * L.wires.length) (south : Bool) :
    1 < L.level i south ∧ L.level i south + 1 < L.height - 1 := by
  cases south <;> unfold level height shift <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    omega

theorem wireY_bounds (L : Layout) {i : ℕ} (hi : i < L.wires.length) (e : Wire) :
    1 < L.wireY i e ∧ L.wireY i e + 1 < L.height - 1 :=
  L.level_bounds (by omega) e.sourceSouth

theorem wireV_bounds (L : Layout) {i : ℕ} (hi : i < L.wires.length) (e : Wire) :
    1 < L.wireV i e ∧ L.wireV i e + 1 < L.height - 1 :=
  L.level_bounds (by omega) (!e.targetSouth)

theorem translated_bounds (L : Layout) {y : ℕ} (hy : y ≤ L.depth) :
    1 < y + L.shift ∧ y + L.shift + 1 < L.height - 1 := by
  unfold height shift
  omega

theorem wirePins_interior (L : Layout) {i : ℕ} (hi : i < L.wires.length) (e : Wire)
    (hs : e.source ≤ L.depth) (ht : e.target ≤ L.depth) {p : ℕ × ℕ}
    (hp : p ∈ L.wirePins i e) :
    0 < p.1 ∧ p.1 < L.width - 1 ∧ 0 < p.2 ∧ p.2 < L.height - 1 := by
  have hx := L.wirePins_column_band i e hp
  have hy := L.wireY_bounds hi e
  have hv := L.wireV_bounds hi e
  have hs := L.translated_bounds hs
  have ht := L.translated_bounds ht
  simp only [wirePins, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp [beside, width, rackX, wireA, wireB, wireC] at hx ⊢ <;>
    (try split_ifs) <;> omega

theorem wirePath_interior (L : Layout) {i : ℕ} (hi : i < L.wires.length) (e : Wire)
    (hs : e.source ≤ L.depth) (ht : e.target ≤ L.depth) {p : ℕ × ℕ}
    (hp : p ∈ L.wirePath i e) :
    0 < p.1 ∧ p.1 < L.width - 1 ∧ 0 < p.2 ∧ p.2 < L.height - 1 := by
  have hy := L.wireY_bounds hi e
  have hv := L.wireV_bounds hi e
  have hs := L.translated_bounds hs
  have ht := L.translated_bounds ht
  simp only [wirePath, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp [wireA, wireB, wireC, width, rackX] <;> omega

private theorem Fits.pins_interior {L : Layout} (h : L.Fits) {p : ℕ × ℕ} (hp : p ∈ L.pins) :
    0 < p.1 ∧ p.1 < L.width - 1 ∧ 0 < p.2 ∧ p.2 < L.height - 1 := by
  obtain ⟨⟨e, i⟩, he, hp⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hp)
  obtain ⟨hi, heq⟩ := List.mem_zipIdx' he
  have hem : e ∈ L.wires := heq.symm ▸ List.getElem_mem _
  exact L.wirePins_interior hi e (h.wires e hem).1 (h.wires e hem).2 hp

theorem Fits.rack_interior {L : Layout} (h : L.Fits) {p : ℕ × ℕ} (hp : p ∈ L.rack) :
    0 < p.1 ∧ p.1 < L.width - 1 ∧ 0 < p.2 ∧ p.2 < L.height - 1 := by
  simp only [Layout.rack, List.mem_toFinset, List.mem_append, List.mem_map, List.mem_flatMap] at hp
  rcases hp with ⟨y, hy, rfl⟩ | ⟨y, hy, hp⟩
  · have hy := L.translated_bounds (h.rack y hy)
    dsimp
    unfold width rackX
    omega
  · have hy := L.translated_bounds (h.dividers y hy)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp <;> unfold width rackX <;> omega

private theorem Fits.blockers_interior {L : Layout} (h : L.Fits) {p : ℕ × ℕ}
    (hp : p ∈ L.blockers) :
    0 < p.1 ∧ p.1 < L.width - 1 ∧ 0 < p.2 ∧ p.2 < L.height - 1 := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
  have hb : y ≤ L.depth := by
    rcases List.mem_append.mp hy with hy | hy
    · exact h.dividers y hy
    · exact h.caps y hy
  have hy := L.translated_bounds hb
  dsimp
  unfold width rackX
  omega

theorem Fits.fixed_interior {L : Layout} (h : L.Fits) {p : ℕ × ℕ} (hp : p ∈ L.fixed) :
    0 < p.1 ∧ p.1 < L.width - 1 ∧ 0 < p.2 ∧ p.2 < L.height - 1 := by
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · exact h.pins_interior hp
    · exact h.rack_interior hp
  · exact h.blockers_interior hp

theorem Fits.goalsRaw_interior {L : Layout} (h : L.Fits) {p : ℕ × ℕ}
    (hp : p ∈ L.goalsRaw) :
    0 < p.1 ∧ p.1 < L.width - 1 ∧ 0 < p.2 ∧ p.2 < L.height - 1 := by
  rcases Finset.mem_union.mp hp with hp | hp
  · exact h.fixed_interior hp
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    have hb : y ≤ L.depth := by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h.stop
      · exact h.goalRows y hy
    have hy := L.translated_bounds hb
    dsimp
    unfold width rackX
    omega

end PushPuzzle.PushPush.Doors.Layout
