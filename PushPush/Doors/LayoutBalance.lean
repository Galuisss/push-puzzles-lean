/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.LayoutGeometry
import Mathlib.Data.List.Nodup

/-! Equal-cardinality storage targets for rack layouts. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Layout

open PushFS (Cell)

private theorem raster_union (L : Layout) (xs ys : Finset (ℕ × ℕ)) :
    L.raster (xs ∪ ys) = L.raster xs ∪ L.raster ys := by
  ext p
  simp

theorem raster_disjoint (L : Layout) {xs ys : Finset (ℕ × ℕ)} (hd : Disjoint xs ys) :
    Disjoint (L.raster xs) (L.raster ys) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp hd ((L.mem_raster _ _).mp hp) ((L.mem_raster _ _).mp hq)

theorem raster_card (L : Layout) (xs : Finset (ℕ × ℕ))
    (hb : ∀ p ∈ xs, p.1 < L.width ∧ p.2 < L.height) :
    (L.raster xs).card = xs.card := by
  let value : Cell L.width L.height → ℕ × ℕ := fun p => (p.1.val, p.2.val)
  have hinj : Function.Injective value := by
    intro p q he
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  have him : (L.raster xs).image value = xs := by
    ext p
    constructor
    · intro hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact (L.mem_raster _ _).mp hq
    · intro hp
      refine Finset.mem_image.mpr
        ⟨(⟨p.1, (hb p hp).1⟩, ⟨p.2, (hb p hp).2⟩), ?_, rfl⟩
      exact (L.mem_raster _ _).mpr hp
  exact (Finset.card_image_of_injective _ hinj).symm.trans (congrArg Finset.card him)

/-- A list of rows at the common working column. -/
def rowStock (L : Layout) (rows : List ℕ) : Finset (ℕ × ℕ) :=
  (rows.map fun y => (L.rackX - 1, y + L.shift)).toFinset

private theorem rowStock_card (L : Layout) (rows : List ℕ) (hd : rows.Nodup) :
    (L.rowStock rows).card = rows.length := by
  unfold rowStock
  rw [List.toFinset_card_of_nodup]
  · simp
  · exact hd.map (fun _ _ he => Nat.add_right_cancel (congrArg Prod.snd he))

private theorem rowStock_fit (L : Layout) (rows : List ℕ) (hb : ∀ y ∈ rows, y ≤ L.depth) :
    ∀ p ∈ L.rowStock rows, p.1 < L.width ∧ p.2 < L.height := by
  intro p hp
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
  have hy := hb y hy
  dsimp
  unfold width height shift
  omega

private theorem rowStock_disjoint_fixed (L : Layout) (rows : List ℕ)
    (hfree : ∀ y ∈ rows, y ∉ L.dividers ++ L.caps) : Disjoint L.fixed (L.rowStock rows) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · have hx := L.pins_west hp
      have hr : 0 < L.rackX := by unfold rackX; omega
      dsimp at hx
      omega
    · have hx := L.rack_column hp
      have hr : 0 < L.rackX := by unfold rackX; omega
      dsimp at hx
      omega
  · obtain ⟨z, hz, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    have hzy := Nat.add_right_cancel (congrArg Prod.snd he)
    exact hfree y hy (hzy ▸ hz)

/-- Dynamic door and signal rows suffice to certify equal initial and target inventories. -/
structure Balanced (L : Layout) : Prop where
  /-- Every initial mobile box has its own row. -/
  initial_nodup : (L.launch :: L.dataRows).Nodup
  /-- Every target mobile box has its own row. -/
  goal_nodup : (L.stop :: L.goalRows).Nodup
  /-- Initial mobile boxes are separate from dividers and caps. -/
  initial_free : ∀ y ∈ L.launch :: L.dataRows, y ∉ L.dividers ++ L.caps
  /-- Target mobile boxes are separate from dividers and caps. -/
  goal_free : ∀ y ∈ L.stop :: L.goalRows, y ∉ L.dividers ++ L.caps
  /-- Initial mobile rows fit in the chamber stack. -/
  initial_fit : ∀ y ∈ L.launch :: L.dataRows, y ≤ L.depth
  /-- Target mobile rows fit in the chamber stack. -/
  goal_fit : ∀ y ∈ L.stop :: L.goalRows, y ≤ L.depth
  /-- There is one final slot for every original stored door bit. -/
  count : L.dataRows.length = L.goalRows.length

theorem Balanced.card_eq {L : Layout} (h : L.Balanced) :
    (L.raster L.initialRaw).card = (L.raster L.goalsRaw).card := by
  change (L.raster (L.fixed ∪ L.rowStock (L.launch :: L.dataRows))).card =
    (L.raster (L.fixed ∪ L.rowStock (L.stop :: L.goalRows))).card
  rw [L.raster_union, L.raster_union,
    Finset.card_union_of_disjoint (L.raster_disjoint (L.rowStock_disjoint_fixed _ h.initial_free)),
    Finset.card_union_of_disjoint (L.raster_disjoint (L.rowStock_disjoint_fixed _ h.goal_free)),
    L.raster_card _ (L.rowStock_fit _ h.initial_fit),
    L.raster_card _ (L.rowStock_fit _ h.goal_fit),
    L.rowStock_card _ h.initial_nodup, L.rowStock_card _ h.goal_nodup]
  simp only [List.length_cons, h.count]

end PushPuzzle.PushPush.Doors.Layout
