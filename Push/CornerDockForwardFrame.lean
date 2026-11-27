/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CornerDockLift
import all Push.CornerDockForward

/-! The concrete southwest docking route preserves the complete live source bitmap. -/

public section
namespace PushPuzzle.Push.CornerDock.Input

open PushFS PushS

variable (r : Input)

private theorem final_walk_frame (s : HoleState r.width r.height) :
    ∃ t : HoleState r.outputWidth r.outputHeight,
      Reachable r.compile.board none (r.stage s r.distance le_rfl).toState t.toState ∧
      t.player = r.target ∧ t.empty = (r.stage s r.distance le_rfl).empty := by
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
    exact ⟨rfl, Fin.ext hg⟩) r.compile.board r.compile.walls_empty none
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
  exact ⟨_, (Relation.ReflTransGen.single ⟨.west, hm⟩).trans hw, rfl, rfl⟩

/-- The actual old-goal-to-corner route changes only the two new western columns. -/
private theorem extend_goal_to_corner_frame (s : HoleState r.width r.height)
    (hp : s.player = r.sourceGoal) :
    ∃ t : HoleState r.outputWidth r.outputHeight,
      Reachable r.compile.board none (r.extend s).toState t.toState ∧ t.player = r.target ∧
      ∀ q : Cell r.width r.height, r.embed q ∈ t.empty ↔ q ∈ s.empty := by
  have he : r.entry ∈ (r.extend s).empty := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  have hm := (r.extend s).walk_move he (d := .west) (by
    change Adjacent .west (r.embed s.player) r.entry
    rw [hp]
    exact ⟨rfl, rfl⟩) r.compile.board r.compile.walls_empty none
  obtain ⟨t, ht, hp', hf⟩ := r.final_walk_frame s
  have hbegin : Reachable r.compile.board none (r.extend s).toState
      (r.stage s 0 (by omega)).toState := by
    rw [← r.stage_zero s he]
    exact Relation.ReflTransGen.single ⟨.west, hm⟩
  refine ⟨t, (hbegin.trans (r.stage_reachable s r.distance le_rfl)).trans ht, hp', ?_⟩
  intro q
  rw [hf]
  simp only [stage, Finset.mem_union, Finset.mem_image, r.embed_injective.eq_iff, exists_eq_right]
  have hx : ¬ ((r.embed q).1.val = 0 ∨ (r.embed q).1.val = 1) := by
    change ¬ (q.1.val + 2 = 0 ∨ q.1.val + 2 = 1)
    omega
  simp only [stageAux, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- A complete live-source solution lifts to the dock corner without changing any source cell. -/
theorem compile_run_frame {s : State r.width r.height}
    (hr : Reachable r.source.board none r.initial.toState s) (hp : s.player = r.sourceGoal) :
    ∃ t : HoleState r.outputWidth r.outputHeight,
      Reachable r.compile.board none r.compile.initial t.toState ∧ t.player = r.target ∧
      ∀ q : Cell r.width r.height, r.embed q ∈ t.empty ↔ q ∈ holes s := by
  let A : HoleState r.width r.height :=
    ⟨s.player, holes s, player_mem_holes (hr.valid r.source.initial_valid)⟩
  have hA : A.toState = s := by
    apply State.ext
    · rfl
    · simp only [HoleState.toState, A, holes, compl_compl]
  let B : Board r.outputWidth r.outputHeight := r.compile.board
  have hpre : Reachable B none (r.liftState r.initial.toState) (r.liftState s) := r.lift_reachable hr
  rw [← hA, r.liftState_toState r.initial, r.liftState_toState A] at hpre
  obtain ⟨t, ht, htp, hframe⟩ := r.extend_goal_to_corner_frame A hp
  exact ⟨t, hpre.trans ht, htp, hframe⟩

end PushPuzzle.Push.CornerDock.Input
