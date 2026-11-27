/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.DockCrop
public import PushPush.Basic
import all Push.CornerDockReverse

/-! The original maximum-sliding source prefix of a successful dock computation. -/

@[expose] public section
namespace PushPuzzle.PushPush.CornerDock

open PushFS (Cell State)

variable (r : Push.CornerDock.Input)

private theorem first_exit_goal {s t : State r.outputWidth r.outputHeight}
    (hpre : Relation.ReflTransGen (SourceStep r) r.compile.initial s)
    (hm : Step s t) (hout : ¬r.SourceInside t) :
    s.player = r.embed r.sourceGoal ∧ r.entry ∈ PushS.holes s := by
  have hp := source_prefix_expansion r hpre
  have hs := r.sourceInside_prefix hp
  obtain ⟨d, hm⟩ := hm
  cases hm with
  | walk hv ha he hb =>
    exact r.first_exit_goal hp hs ⟨d, .walk
      ⟨Finset.notMem_empty _, Finset.disjoint_empty_right _, hv⟩ ha
      (Finset.notMem_empty _) he hb⟩ hout
  | push hv hn hk slide hplayer hb =>
    apply False.elim
    apply hout
    have hi := slide_players_inside r slide hn hk hp hs ⟨1, by omega⟩
    change 2 ≤ (slide.cell ⟨1, by omega⟩).1.val ∧
      (slide.cell ⟨1, by omega⟩).2.val < r.height at hi
    change 2 ≤ t.player.1.val ∧ t.player.2.val < r.height
    simpa only [hplayer] using hi

/-- The source goal and exact source boxes on the actual maximum-game trace. -/
structure GoalPrefix (finish : State r.outputWidth r.outputHeight) where
  state : State r.outputWidth r.outputHeight
  before : Relation.ReflTransGen (SourceStep r) r.compile.initial state
  after : Reachable state finish
  player : state.player = r.embed r.sourceGoal
  entry_empty : r.entry ∈ PushS.holes state
  reachable : Reachable r.initial.toState (r.sourceState state)

theorem goalPrefix {finish : State r.outputWidth r.outputHeight}
    (hr : Reachable r.compile.initial finish) (ht : finish.player = r.target) :
    Nonempty (GoalPrefix r finish) := by
  obtain ⟨s, t, hpre, _, hm, hout, hrest⟩ := Push.Path.first_exit
    (P := r.SourceInside) hr (by change 2 ≤ r.initial.player.1.val + 2 ∧ _; exact
      ⟨by omega, r.initial.player.2.isLt⟩) (by
      intro hi
      have hx := hi.1
      rw [ht] at hx
      change 2 ≤ 0 at hx
      omega)
  obtain ⟨hg, he⟩ := first_exit_goal r hpre hm hout
  refine ⟨⟨s, hpre, (Relation.ReflTransGen.single hm).trans hrest, hg, he, ?_⟩⟩
  simpa only [r.sourceState_initial] using sourceState_between r .refl hpre he

end PushPuzzle.PushPush.CornerDock
