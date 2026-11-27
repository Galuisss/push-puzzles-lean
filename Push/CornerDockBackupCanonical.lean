/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CornerDockForwardFrame
import all Push.CornerDockForward
import all Push.CornerDockForwardFrame

/-! The canonical southwest dock endpoint retains its complete return corridors. -/

public section
namespace PushPuzzle.Push.CornerDock.Backup

open PushFS PushS

/-- Exact source holes and the two walkways retained by the actual canonical docking route. -/
structure Ready (r : Input) (s : State r.width r.height)
    (t : HoleState r.outputWidth r.outputHeight) : Prop where
  source : ∀ q : Cell r.width r.height, r.embed q ∈ t.empty ↔ q ∈ holes s
  western : ∀ q : Cell r.outputWidth r.outputHeight, q.1.val = 0 → r.height ≤ q.2.val → q ∈ t.empty
  corridor : ∀ q : Cell r.outputWidth r.outputHeight, q.1.val = 1 →
    r.goalY.val ≤ q.2.val → q.2.val ≤ r.height → q ∈ t.empty

private theorem stage_ready (r : Input) (s : HoleState r.width r.height) :
    Ready r s.toState (r.stage s r.distance le_rfl) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    rw [s.holes_toState]
    simp only [Input.stage, Finset.mem_union, Finset.mem_image, r.embed_injective.eq_iff, exists_eq_right]
    have hx : 2 ≤ (r.embed q).1.val := by change 2 ≤ q.1.val + 2; omega
    simp only [Input.stageAux, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (hq | hq)
      · exact hq
      · omega
    · exact Or.inl
  · intro q hx hy
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨hx, hy⟩⟩)
  · intro q hx hlo hhi
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, Or.inr ⟨hx, Or.inl ⟨hlo, by have := r.height_eq; omega⟩⟩⟩

/-- The physical goal-to-corner macro reaches a state with the exact source bitmap and usable return walkways. -/
private theorem goal_to_ready (r : Input) (s : HoleState r.width r.height)
    (hp : s.player = r.sourceGoal) :
    ∃ t : HoleState r.outputWidth r.outputHeight,
      Reachable r.compile.board none (r.extend s).toState t.toState ∧
      t.player = r.target ∧ Ready r s.toState t := by
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
  have hs := stage_ready r s
  exact ⟨fun q => by rw [hf]; exact hs.source q,
    fun q hx hy => by rw [hf]; exact hs.western q hx hy,
    fun q hx hlo hhi => by rw [hf]; exact hs.corridor q hx hlo hhi⟩

/-- A real source solution followed by canonical docking retains the literal walkways. -/
theorem compile_ready (r : Input) {s : State r.width r.height}
    (hr : Reachable r.source.board none r.initial.toState s) (hp : s.player = r.sourceGoal) :
    ∃ t : HoleState r.outputWidth r.outputHeight,
      Reachable r.compile.board none r.compile.initial t.toState ∧ t.player = r.target ∧ Ready r s t := by
  let A : HoleState r.width r.height :=
    ⟨s.player, holes s, player_mem_holes (hr.valid r.source.initial_valid)⟩
  have hA : A.toState = s := by
    apply State.ext
    · rfl
    · simp only [HoleState.toState, A, holes, compl_compl]
  let B : Board r.outputWidth r.outputHeight := r.compile.board
  have hpre : Reachable B none (r.liftState r.initial.toState) (r.liftState s) := r.lift_reachable hr
  rw [← hA, r.liftState_toState r.initial, r.liftState_toState A] at hpre
  obtain ⟨t, ht, htp, hready⟩ := goal_to_ready r A hp
  exact ⟨t, hpre.trans ht, htp, hA ▸ hready⟩

end PushPuzzle.Push.CornerDock.Backup
