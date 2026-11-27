/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Basic
public import PushS.HoleState

/-! The southwest dock for a source game whose player target is on its left boundary. -/

@[expose] public section
namespace PushPuzzle.Push.CornerDock

open PushFS PushS

/-- A live wall-free source state with a left-boundary target row. -/
structure Input where
  width : ℕ
  height : ℕ
  initial : HoleState width height
  goalY : Fin height

namespace Input

variable (r : Input)

theorem width_pos : 0 < r.width := Nat.zero_lt_of_lt r.initial.player.1.isLt
theorem height_pos : 0 < r.height := Nat.zero_lt_of_lt r.initial.player.2.isLt

/-- Distance from the old target row to the first added southern row. -/
def distance : ℕ := r.height - r.goalY.val

theorem distance_pos : 0 < r.distance := by have := r.goalY.isLt; dsimp [distance]; omega

/-- Add the two western dock columns. -/
def outputWidth : ℕ := r.width + 2
/-- Add one target-to-bottom distance below the original source. -/
def outputHeight : ℕ := r.height + r.distance

/-- The original player target, restricted to the left boundary. -/
def sourceGoal : Cell r.width r.height := (⟨0, r.width_pos⟩, r.goalY)

/-- The source game whose accepting player cell is the specified left-boundary target. -/
def source : Push.Instance where
  width := r.width
  height := r.height
  initial := r.initial.toState
  target := r.sourceGoal
  player_empty := by simpa only [HoleState.toState, Finset.mem_compl, not_not] using
    r.initial.player_empty

/-- The source rectangle is translated two columns to the east. -/
def embed (q : Cell r.width r.height) : Cell r.outputWidth r.outputHeight :=
  (⟨q.1.val + 2, by have := q.1.isLt; dsimp [outputWidth]; omega⟩,
    ⟨q.2.val, by have := q.2.isLt; dsimp [outputHeight]; omega⟩)

theorem embed_injective : Function.Injective r.embed := by
  intro p q he
  have hx := congrArg (fun q => q.1.val) he
  have hy := congrArg (fun q => q.2.val) he
  apply Prod.ext <;> apply Fin.ext
  · change p.1.val + 2 = q.1.val + 2 at hx
    omega
  · exact hy

/-- The unique westward exit from the old target row. -/
def entry : Cell r.outputWidth r.outputHeight :=
  (⟨1, by dsimp [outputWidth]; omega⟩,
    ⟨r.goalY.val, by have := r.goalY.isLt; dsimp [outputHeight]; omega⟩)

/-- The two new southern walkway columns. -/
def walkHoles : Finset (Cell r.outputWidth r.outputHeight) :=
  Finset.univ.filter fun q => q.1.val < 2 ∧ r.height ≤ q.2.val

/-- All fixed new holes; the source state itself remains live. -/
def auxiliaryHoles : Finset (Cell r.outputWidth r.outputHeight) := insert r.entry r.walkHoles

/-- Extend any live source state by this same physical dock. -/
def extend (s : HoleState r.width r.height) : HoleState r.outputWidth r.outputHeight where
  player := r.embed s.player
  empty := s.empty.image r.embed ∪ r.auxiliaryHoles
  player_empty := Finset.mem_union_left _ (Finset.mem_image.mpr
    ⟨s.player, s.player_empty, rfl⟩)

/-- The southwest corner of the expanded rectangle. -/
def target : Cell r.outputWidth r.outputHeight :=
  (⟨0, by dsimp [outputWidth]; omega⟩,
    ⟨r.outputHeight - 1, by have := r.height_pos; dsimp [outputHeight]; omega⟩)

/-- The actual ordinary no-wall player-target instance with the southwest dock. -/
def compile : Push.Instance where
  width := r.outputWidth
  height := r.outputHeight
  initial := (r.extend r.initial).toState
  target := r.target
  player_empty := by simpa only [HoleState.toState, Finset.mem_compl, not_not] using
    (r.extend r.initial).player_empty

@[simp] theorem embed_mem_extend (s : HoleState r.width r.height) (q : Cell r.width r.height) :
    r.embed q ∈ (r.extend s).empty ↔ q ∈ s.empty := by
  have hqx : 2 ≤ (r.embed q).1.val := by change 2 ≤ q.1.val + 2; omega
  have he : r.embed q ≠ r.entry := by
    intro hh
    have := congrArg (fun q => q.1.val) hh
    change q.1.val + 2 = 1 at this
    omega
  simp only [extend, Finset.mem_union, Finset.mem_image, r.embed_injective.eq_iff, exists_eq_right]
  simp only [auxiliaryHoles, Finset.mem_insert, walkHoles, Finset.mem_filter,
    Finset.mem_univ, true_and, he, false_or]
  have hn : ¬ (r.embed q).1.val < 2 := by omega
  simp only [hn, false_and, or_false]

/-- Above the original bottom, the sole new west hole is the target-row exit. -/
theorem west_holes_on_source_rows (s : HoleState r.width r.height)
    (q : Cell r.outputWidth r.outputHeight) (hx : q.1.val < 2) (hy : q.2.val < r.height) :
    q ∈ (r.extend s).empty ↔ q = r.entry := by
  simp only [extend, Finset.mem_union, auxiliaryHoles, Finset.mem_insert,
    walkHoles, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (he | he | he)
    · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp he
      have hax := congrArg (fun q => q.1.val) ha
      change a.1.val + 2 = q.1.val at hax
      omega
    · exact he
    · omega
  · exact fun he => Or.inr (Or.inl he)

end Input
end PushPuzzle.Push.CornerDock
