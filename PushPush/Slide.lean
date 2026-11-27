/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Run

/-! Maximum sliding of a complete box run on a wall-free rectangle. -/

@[expose] public section

namespace PushPuzzle.PushPush

open PushFS (Cell Direction Adjacent State)

variable {w h n k : ℕ} {d : Direction} {s t : State w h}

/-- The player, a complete run of `n` boxes, and `k` clear cells up to its stop.
The cell beyond the stop is occupied or lies outside the rectangle. -/
structure Slide (d : Direction) (s : State w h) (n k : ℕ) where
  /-- Cells from the original player to the final leading box. -/
  cell : Fin (n + k + 1) → Cell w h
  /-- The ray begins at the original player. -/
  start : cell 0 = s.player
  /-- Every ray step follows the chosen direction. -/
  adjacent : ∀ i : Fin (n + k), Adjacent d (cell i.castSucc) (cell i.succ)
  /-- The initial consecutive run. -/
  occupied : ∀ i : Fin n, cell ⟨i.val + 1, by omega⟩ ∈ s.boxes
  /-- All cells traversed beyond the original run are clear. -/
  clear : ∀ i : Fin k, cell ⟨n + i.val + 1, by omega⟩ ∉ s.boxes
  /-- The entire run stops against another box or the true boundary. -/
  stopped : ∀ q, Adjacent d (cell ⟨n + k, by omega⟩) q → q ∈ s.boxes

namespace Slide

theorem position (r : Slide d s n k) (i : Fin (n + k + 1)) :
    d.position (r.cell i) = d.position s.player + i.val := by
  induction i using Fin.induction with
  | zero => simp only [r.start, Fin.val_zero, Int.natCast_zero, Int.add_zero]
  | succ i ih =>
    have ha := (r.adjacent i).position
    simp only [Fin.val_succ, Fin.val_castSucc] at *
    rw [ha, ih]
    omega

theorem lane (r : Slide d s n k) (i : Fin (n + k + 1)) :
    d.lane (r.cell i) = d.lane s.player := by
  induction i using Fin.induction with
  | zero => rw [r.start]
  | succ i ih => exact (r.adjacent i).lane.trans ih

theorem injective (r : Slide d s n k) : Function.Injective r.cell := by
  intro i j he
  have hi := r.position i
  have hj := r.position j
  rw [he] at hi
  apply Fin.ext
  omega

/-- The initial moving box set. -/
def before (r : Slide d s n k) : Finset (Cell w h) :=
  Finset.univ.image fun i : Fin n => r.cell ⟨i.val + 1, by omega⟩

/-- The same run translated by its full positive sliding distance. -/
def after (r : Slide d s n k) : Finset (Cell w h) :=
  Finset.univ.image fun i : Fin n => r.cell ⟨k + i.val + 1, by omega⟩

/-- Move exactly the initial run, preserving all other boxes. -/
def boxes (r : Slide d s n k) : Finset (Cell w h) :=
  (s.boxes \ r.before) ∪ r.after

theorem before_subset (r : Slide d s n k) : r.before ⊆ s.boxes := by
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact r.occupied i

theorem card_before (r : Slide d s n k) : r.before.card = n := by
  rw [before, Finset.card_image_of_injective]
  · simp
  · intro i j he
    have he := congrArg Fin.val (r.injective he)
    exact Fin.ext (by simpa using he)

theorem card_after (r : Slide d s n k) : r.after.card = n := by
  rw [after, Finset.card_image_of_injective]
  · simp
  · intro i j he
    have he := congrArg Fin.val (r.injective he)
    apply Fin.ext
    change k + i.val + 1 = k + j.val + 1 at he
    omega

theorem after_disjoint (r : Slide d s n k) : Disjoint (s.boxes \ r.before) r.after := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hbox, hnot⟩ := Finset.mem_sdiff.mp hp
  by_cases hi : k + i.val < n
  · apply hnot
    exact Finset.mem_image.mpr ⟨⟨k + i.val, hi⟩, Finset.mem_univ _, rfl⟩
  · have he : (⟨n + (k + i.val - n) + 1, by omega⟩ : Fin (n + k + 1)) =
        ⟨k + i.val + 1, by omega⟩ := Fin.ext (by
          change n + (k + i.val - n) + 1 = k + i.val + 1
          omega)
    exact r.clear ⟨k + i.val - n, by omega⟩ (he ▸ hbox)

private theorem card_boxes (r : Slide d s n k) : r.boxes.card = s.boxes.card := by
  rw [boxes, Finset.card_union_of_disjoint r.after_disjoint,
    Finset.card_sdiff_of_subset r.before_subset, r.card_before, r.card_after]
  have := Finset.card_le_card r.before_subset
  rw [r.card_before] at this
  omega

theorem player_empty (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k) :
    r.cell ⟨1, by omega⟩ ∉ r.boxes := by
  intro hp
  rcases Finset.mem_union.mp hp with hp | hp
  · have hnot := (Finset.mem_sdiff.mp hp).2
    exact hnot (Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩)
  · obtain ⟨i, _, he⟩ := Finset.mem_image.mp hp
    have := congrArg Fin.val (r.injective he)
    change k + i.val + 1 = 1 at this
    omega

end Slide

/-- A walk, or one maximum slide; the player advances exactly one cell. -/
inductive Move (d : Direction) : State w h → State w h → Prop
  | walk {s t : State w h} (valid : s.player ∉ s.boxes)
      (adjacent : Adjacent d s.player t.player)
      (empty : t.player ∉ s.boxes) (boxes : t.boxes = s.boxes) : Move d s t
  | push {s t : State w h} {n k : ℕ} (valid : s.player ∉ s.boxes) (positive : 0 < n)
      (distance : 0 < k) (slide : Slide d s n k)
      (player : t.player = slide.cell ⟨1, by omega⟩)
      (boxes : t.boxes = slide.boxes) : Move d s t

/-- One legal walk or maximum slide in any direction. -/
def Step (s t : State w h) : Prop := ∃ d, Move d s t

/-- Finite maximum-slide trajectories, including the empty trajectory. -/
abbrev Reachable := Relation.ReflTransGen (@Step w h)

theorem Move.valid_target (hm : Move d s t) : t.player ∉ t.boxes := by
  cases hm with
  | walk _ _ he hb => exact hb ▸ he
  | push _ hn hk r hp hb => rw [hp, hb]; exact r.player_empty hn hk

private theorem Move.card_boxes (hm : Move d s t) : t.boxes.card = s.boxes.card := by
  cases hm with
  | walk _ _ _ hb => exact congrArg Finset.card hb
  | push _ _ _ r _ hb => rw [hb]; exact r.card_boxes

theorem Reachable.valid (hr : Reachable s t) (hs : s.player ∉ s.boxes) :
    t.player ∉ t.boxes := by
  induction hr with
  | refl => exact hs
  | tail _ hm _ => exact hm.choose_spec.valid_target

theorem Reachable.card_boxes (hr : Reachable s t) : t.boxes.card = s.boxes.card := by
  induction hr with
  | refl => rfl
  | tail _ hm ih => exact hm.choose_spec.card_boxes.trans ih

theorem Reachable.card_holes (hr : Reachable s t) : t.boxesᶜ.card = s.boxesᶜ.card := by
  simp only [Finset.card_compl, hr.card_boxes]

end PushPuzzle.PushPush
