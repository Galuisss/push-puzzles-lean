/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.DockFrame
public import PushPush.ColumnReaderRuns
public import Push.CyclicOriginalHoles

/-! Cyclic commitments retain a maximum-sliding source computation and whole-run consumption. -/

@[expose] public section
namespace PushPuzzle.PushPush.Cyclic

open PushFS (Cell State)
open Push.Cyclic Push.StripFrontier

variable (r : Push.ColumnScan.Input)

private theorem lift_reader_path {s t : State (wideReader r).outputWidth
    (wideReader r).outputHeight}
    (hr : PushFS.Reachable (wideReader r).compile.board none s t) :
    Relation.ReflTransGen (dock r).SourceStep ((dock r).liftState s) ((dock r).liftState t) := by
  exact hr.lift (dock r).liftState (fun a b ⟨d, hm⟩ => ⟨⟨d, (dock r).lift_move hm⟩, by
    change 2 ≤ b.player.1.val + 2 ∧ b.player.2.val < (wideReader r).outputHeight
    exact ⟨by omega, b.player.2.isLt⟩⟩)

/-- A geometric commitment paired with its genuine maximum-game source path. -/
structure Commit (finish : State (dock r).outputWidth (dock r).outputHeight) where
  trace : Push.Cyclic.Commit r finish
  source : Reachable r.initial.toState trace.sourceState
  after : Reachable trace.readerEnd finish
  reader_whole : ColumnReader.NoNorthSplit (PushS.holes trace.sourceState)
    (originalHoles r trace.readerEnd)

theorem exists_commit {finish : State (dock r).outputWidth (dock r).outputHeight}
    (hr : Reachable (dock r).compile.initial finish) (ht : finish.player = (dock r).target) :
    Nonempty (Commit r finish) := by
  obtain ⟨g⟩ := CornerDock.goalPrefix (dock r) hr ht
  have hgoal : ((dock r).sourceState g.state).player = (wideReader r).target := by
    apply (dock r).embed_injective
    exact ((dock r).sourceState_player
      ((dock r).sourceInside_prefix (CornerDock.source_prefix_expansion (dock r) g.before))).trans g.player
  have hfx := congrArg (fun p => p.1.val) hgoal
  have hfy := congrArg (fun p => p.2.val) hgoal
  obtain ⟨w⟩ := ColumnReader.source_witness (wideReader r) g.reachable hfx hfy.ge
  have hframe := CornerDock.liftState_sourceState (dock r)
    (CornerDock.source_prefix_expansion (dock r) g.before) g.entry_empty
  have hbefore := lift_reader_path r
    (Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ w.before)
  have hinit : (dock r).liftState (wideReader r).initialState.toState = (dock r).compile.initial :=
    (dock r).liftState_toState (dock r).initial
  rw [hinit] at hbefore
  have huntil := lift_reader_path r w.suffix
  rw [hframe] at huntil
  have hcrop := CornerDock.sourceState_liftState (dock r) w.state
  let c : Push.Cyclic.Commit r finish := {
    state := (dock r).liftState w.state
    readerEnd := g.state
    before := hbefore
    untilGoal := huntil
    afterGoal := g.after.unit_expansion (dock r).compile.board rfl
    readerGoal := hgoal
    entry_empty := g.entry_empty
    readerBefore := by
      exact Eq.mpr (congrArg (fun u => Relation.ReflTransGen
        (NorthStep (wideReader r).compile.board none (wideReader r).width (wideReader r).targetLevel)
        (wideReader r).initialState.toState u) hcrop) w.before
    readerLanding := by
      exact (congrArg State.player hcrop).trans w.landing
  }
  refine ⟨⟨c, ?_, g.after, ?_⟩⟩
  · change Reachable r.initial.toState
      ((wideReader r).cropState ((dock r).sourceState ((dock r).liftState w.state)))
    exact (congrArg (wideReader r).cropState hcrop).symm ▸ w.source
  · have hwhole := (ColumnReader.SourceWitness.whole_remainder (wideReader r) w hfx hfy.ge).no_split
    intro p hp q hq ha
    have hsource : c.sourceState = (wideReader r).cropState w.state := by
      exact congrArg (wideReader r).cropState hcrop
    have hpE : (wideReader r).embed p ∈
        Push.ReflectedFrontier.source r.width r.height w.state := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, p.1.isLt, p.2.isLt⟩
      exact ((wideReader r).cropState_mem_holes w.state p).mp
        (hsource ▸ (Finset.mem_sdiff.mp hp).1)
    have hqF : (wideReader r).embed q ∈
        Push.ReflectedFrontier.source r.width r.height ((dock r).sourceState g.state) := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, q.1.isLt, q.2.isLt⟩
      exact ((dock r).sourceState_hole g.state ((wideReader r).embed q)).mpr
        ((mem_originalHoles r g.state q).mp hq)
    have hpF : (wideReader r).embed p ∉
        Push.ReflectedFrontier.source r.width r.height ((dock r).sourceState g.state) := by
      intro hh
      apply (Finset.mem_sdiff.mp hp).2
      exact (mem_originalHoles r g.state p).mpr
        (((dock r).sourceState_hole g.state ((wideReader r).embed p)).mp (Finset.mem_filter.mp hh).1)
    exact hwhole _ (Finset.mem_sdiff.mpr ⟨hpE, hpF⟩) _ hqF
      ((ColumnReader.embed_adjacent (wideReader r) .north p q).mpr ha)

end PushPuzzle.PushPush.Cyclic
