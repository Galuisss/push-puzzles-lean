/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CornerDock
public import PushS.LineWalking
import all PushS.LinePush

/-! Actual southern pushes and walkway traversal from the old left target to the new corner. -/

@[expose] public section
namespace PushPuzzle.Push.CornerDock.Input

open PushFS PushS

variable (r : Input)

private theorem height_eq : r.height = r.goalY.val + r.distance := by
  have := r.goalY.isLt
  dsimp [distance]
  omega

private def stageAux (k : ℕ) : Finset (Cell r.outputWidth r.outputHeight) :=
  Finset.univ.filter fun q =>
    (q.1.val = 0 ∧ r.height ≤ q.2.val) ∨
    (q.1.val = 1 ∧ ((r.goalY.val ≤ q.2.val ∧ q.2.val ≤ r.goalY.val + k) ∨
      r.height + k ≤ q.2.val))

private def stage (s : HoleState r.width r.height) (k : ℕ) (hk : k ≤ r.distance) :
    HoleState r.outputWidth r.outputHeight where
  player := (⟨1, by dsimp [outputWidth]; omega⟩,
    ⟨r.goalY.val + k, by have := r.height_eq; have := r.distance_pos; dsimp [outputHeight]; omega⟩)
  empty := s.empty.image r.embed ∪ r.stageAux k
  player_empty := Finset.mem_union_right _ (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, Or.inr ⟨rfl, Or.inl
      ⟨by change r.goalY.val ≤ r.goalY.val + k; omega, le_rfl⟩⟩⟩)

private theorem source_x {s : HoleState r.width r.height} {q : Cell r.outputWidth r.outputHeight}
    (hq : q ∈ s.empty.image r.embed) : 2 ≤ q.1.val := by
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hq
  change 2 ≤ a.1.val + 2
  omega

private theorem stage_zero (s : HoleState r.width r.height)
    (he : r.entry ∈ (r.extend s).empty) :
    (r.extend s).walk r.entry he = r.stage s 0 (by omega) := by
  have haux : r.auxiliaryHoles = r.stageAux 0 := by
    ext q
    simp only [auxiliaryHoles, walkHoles, stageAux, Finset.mem_insert, Finset.mem_filter,
      Finset.mem_univ, true_and, entry, Prod.ext_iff, Fin.ext_iff]
    have := r.goalY.isLt
    omega
  cases s
  simp only [HoleState.walk, extend, stage, haux]
  rfl

private def destination (k : ℕ) (hk : k < r.distance) : Cell r.outputWidth r.outputHeight :=
  (⟨1, by dsimp [outputWidth]; omega⟩,
    ⟨r.height + k, by dsimp [outputHeight]; omega⟩)

private theorem stage_update (s : HoleState r.width r.height) {k : ℕ} (hk : k < r.distance)
    (hd : 1 < r.distance) :
    (r.stage s (k + 1) (by omega)).empty =
      insert (r.stage s (k + 1) (by omega)).player
        ((r.stage s k (by omega)).empty.erase (r.destination k hk)) := by
  ext q
  by_cases hs : q ∈ s.empty.image r.embed
  · have hx := r.source_x hs
    simp only [stage, Finset.mem_union, Finset.mem_insert, Finset.mem_erase, hs, true_or,
      destination, Ne, Prod.ext_iff, Fin.ext_iff]
    simp only [true_iff, and_true]
    right
    rintro ⟨hxx, _⟩
    omega
  · simp only [stage, stageAux, Finset.mem_union, Finset.mem_insert, Finset.mem_erase,
      Finset.mem_filter, Finset.mem_univ, true_and, hs, false_or]
    simp only [destination, Ne, Prod.ext_iff, Fin.ext_iff]
    have := r.height_eq
    omega

private theorem stage_walk (s : HoleState r.width r.height) {k : ℕ} (hk : k < r.distance)
    (hd : r.distance = 1) : Move r.compile.board none .south (r.stage s k (by omega)).toState
      (r.stage s (k + 1) (by omega)).toState := by
  have hg := r.height_eq
  refine Move.walk ((r.stage s k (by omega)).valid _ r.compile.walls_empty) ?_ (by simp) ?_ ?_
  · exact ⟨rfl, by change r.goalY.val + (k + 1) = r.goalY.val + k + 1; omega⟩
  · apply Finset.notMem_compl.mpr
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Or.inr ⟨rfl, Or.inr ?_⟩⟩
    change r.height + k ≤ r.goalY.val + (k + 1)
    omega
  · change (s.empty.image r.embed ∪ r.stageAux (k + 1))ᶜ =
      (s.empty.image r.embed ∪ r.stageAux k)ᶜ
    congr 2
    ext q
    simp only [stageAux, Finset.mem_filter, Finset.mem_univ, true_and]
    have := q.2.isLt
    change q.2.val < r.height + r.distance at this
    omega

private theorem stage_move (s : HoleState r.width r.height) {k : ℕ} (hk : k < r.distance) :
    Step r.compile.board none (r.stage s k (by omega)).toState
      (r.stage s (k + 1) (by omega)).toState := by
  have hg := r.height_eq
  by_cases hd : r.distance = 1
  · exact ⟨.south, r.stage_walk s hk hd⟩
  · refine ⟨.south, HoleState.move_to_first_hole _ _ .south (r.destination k hk)
      (r.distance - 1) (by have := r.distance_pos; omega) rfl ?_ ?_ ?_ ?_
        (r.stage_update s hk (by have := r.distance_pos; omega)) _ r.compile.walls_empty⟩
    · change (r.height + k : ℕ) = (r.goalY.val + k : ℕ) + (r.distance - 1 : ℕ) + (1 : ℤ)
      have := r.distance_pos
      omega
    · intro q hl hlo hhi hq
      have hx : q.1.val = 1 := hl
      change (r.goalY.val + k : ℕ) < (q.2.val : ℤ) at hlo
      change (q.2.val : ℤ) < (r.height + k : ℕ) at hhi
      simp only [stage, Finset.mem_union] at hq
      rcases hq with hs | ha
      · have := r.source_x hs
        omega
      · have := (Finset.mem_filter.mp ha).2
        omega
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨rfl, Or.inr le_rfl⟩⟩
    · exact ⟨rfl, by change r.goalY.val + (k + 1) = r.goalY.val + k + 1; omega⟩

private theorem stage_reachable (s : HoleState r.width r.height) (k : ℕ) (hk : k ≤ r.distance) :
    Reachable r.compile.board none (r.stage s 0 (by omega)).toState (r.stage s k hk).toState := by
  induction k with
  | zero => exact .refl
  | succ k ih => exact (ih (by omega)).tail (r.stage_move s (by omega))

private def westEntry : Cell r.outputWidth r.outputHeight :=
  (r.target.1, ⟨r.height, by have := r.distance_pos; dsimp [outputHeight]; omega⟩)

private theorem final_walk (s : HoleState r.width r.height) :
    ∃ t : HoleState r.outputWidth r.outputHeight,
      Reachable r.compile.board none (r.stage s r.distance le_rfl).toState t.toState ∧
      t.player = r.target := by
  have hg := r.height_eq
  let a := r.stage s r.distance le_rfl
  have hentry : r.westEntry ∈ a.empty := Finset.mem_union_right _
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨rfl, le_rfl⟩⟩)
  have htarget : r.target ∈ a.empty := by
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Or.inl ⟨rfl, ?_⟩⟩
    change r.height ≤ r.height + r.distance - 1
    have := r.distance_pos
    omega
  have hm := a.walk_move hentry (d := .west) (by
    change 0 + 1 = 1 ∧ r.westEntry.2 = a.player.2
    refine ⟨rfl, Fin.ext ?_⟩
    exact hg) r.compile.board r.compile.walls_empty none
  have hw := ((a.walk r.westEntry hentry).walk_vertical r.target htarget rfl (by
    intro q hx hlo _
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Or.inl ⟨congrArg Fin.val hx, ?_⟩⟩
    have hle : r.height ≤ r.outputHeight - 1 := by
      have := r.distance_pos
      dsimp [outputHeight]
      omega
    change min r.height (r.outputHeight - 1) ≤ q.2.val at hlo
    rwa [Nat.min_eq_left hle] at hlo) r.compile.board r.compile.walls_empty none).1
  exact ⟨_, (Relation.ReflTransGen.single ⟨.west, hm⟩).trans hw, rfl⟩

/-- From the embedded old left goal, real walks and complete pushes reach the new southwest corner. -/
theorem extend_goal_to_corner (s : HoleState r.width r.height) (hp : s.player = r.sourceGoal) :
    ∃ t : HoleState r.outputWidth r.outputHeight,
      Reachable r.compile.board none (r.extend s).toState t.toState ∧ t.player = r.target := by
  have he : r.entry ∈ (r.extend s).empty :=
    Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  have hm := (r.extend s).walk_move he (d := .west) (by
    change Adjacent .west (r.embed s.player) r.entry
    rw [hp]
    exact ⟨rfl, rfl⟩) r.compile.board r.compile.walls_empty none
  obtain ⟨t, ht, hp'⟩ := r.final_walk s
  have hbegin : Reachable r.compile.board none (r.extend s).toState
      (r.stage s 0 (by omega)).toState := by
    rw [← r.stage_zero s he]
    exact Relation.ReflTransGen.single ⟨.west, hm⟩
  exact ⟨t, (hbegin.trans (r.stage_reachable s r.distance le_rfl)).trans ht, hp'⟩

end PushPuzzle.Push.CornerDock.Input
