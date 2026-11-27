/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Cyclic
public import Push.CornerDockTrace
public import Push.ColumnScanQuotas

/-! Extract the same physical committed source prefix from an actual dock trace. -/

@[expose] public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS StripFrontier

/-- The exact widened-reader state inside an arbitrary physical dock state. -/
def readerState (r : ColumnScan.Input)
    (s : State (dock r).outputWidth (dock r).outputHeight) :
    State (wideReader r).outputWidth (wideReader r).outputHeight := (dock r).sourceState s

private theorem readerState_initial (r : ColumnScan.Input) :
    readerState r (dock r).compile.initial = (wideReader r).initialState.toState :=
  (dock r).sourceState_initial

/-- One actual dock trace, its committed landing, and its later original-reader goal. -/
structure Commit (r : ColumnScan.Input)
    (finish : State (dock r).outputWidth (dock r).outputHeight) where
  state : State (dock r).outputWidth (dock r).outputHeight
  readerEnd : State (dock r).outputWidth (dock r).outputHeight
  before : Relation.ReflTransGen (dock r).SourceStep (dock r).compile.initial state
  untilGoal : Relation.ReflTransGen (dock r).SourceStep state readerEnd
  afterGoal : Reachable (dock r).compile.board none readerEnd finish
  readerGoal : (readerState r readerEnd).player = (wideReader r).target
  entry_empty : (dock r).entry ∈ holes readerEnd
  readerBefore : Relation.ReflTransGen
    (NorthStep (wideReader r).compile.board none (wideReader r).width (wideReader r).targetLevel)
    (wideReader r).initialState.toState (readerState r state)
  readerLanding : (readerState r state).player = (wideReader r).landing

namespace Commit

variable {r : ColumnScan.Input} {finish : State (dock r).outputWidth (dock r).outputHeight}
  (c : Commit r finish)

theorem readerSuffix : Reachable (wideReader r).compile.board none
    (readerState r c.state) (readerState r c.readerEnd) :=
  (dock r).sourceState_between c.before c.untilGoal c.entry_empty

theorem player : c.state.player = (dock r).embed (wideReader r).landing := by
  rw [← (dock r).sourceState_player ((dock r).sourceInside_prefix c.before)]
  exact congrArg (dock r).embed c.readerLanding

theorem suffix : Reachable (dock r).compile.board none c.state finish :=
  (Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ c.untilGoal).trans c.afterGoal

/-- The very same physical commitment has filled the original reader's source door. -/
theorem door_occupied : (dock r).embed (wideReader r).door ∈ c.state.boxes := by
  have hfx : (readerState r c.readerEnd).player.1.val = 0 := congrArg (fun q => q.1.val) c.readerGoal
  have hfy : (readerState r c.readerEnd).player.2.val = (wideReader r).targetLevel :=
    congrArg (fun q => q.2.val) c.readerGoal
  have hdoor := (wideReader r).landing_door_occupied c.readerBefore c.readerSuffix hfx hfy.ge c.readerLanding
  by_contra h
  have hh := ((dock r).sourceState_hole c.state (wideReader r).door).mpr ((mem_holes _).mpr h)
  exact (mem_holes _).mp hh hdoor

end Commit

/-- Every actual dock solution supplies the original column reader's commitment on that same trace. -/
theorem exists_commit (r : ColumnScan.Input)
    {finish : State (dock r).outputWidth (dock r).outputHeight}
    (hr : Reachable (dock r).compile.board none (dock r).compile.initial finish)
    (ht : finish.player = (dock r).target) : Nonempty (Commit r finish) := by
  obtain ⟨goal⟩ := (dock r).goalPrefix hr ht
  have hgoal : (readerState r goal.state).player = (wideReader r).target := by
    apply (dock r).embed_injective
    exact ((dock r).sourceState_player ((dock r).sourceInside_prefix goal.before)).trans goal.player
  have hfSouth : ¬North (wideReader r).width (wideReader r).targetLevel (readerState r goal.state) := by
    intro h
    unfold North at h
    rw [hgoal] at h
    have := h (by change 0 < r.width; exact r.width_pos)
    change (wideReader r).targetLevel < (wideReader r).targetLevel at this
    omega
  have hsNorth : North (wideReader r).width (wideReader r).targetLevel
      (readerState r (dock r).compile.initial) := by
    rw [readerState_initial]
    exact (wideReader r).initial_north _
  obtain ⟨s, t, hpre, hs, hm, htSouth, hrest⟩ := Path.first_exit
    (P := fun u => North (wideReader r).width (wideReader r).targetLevel (readerState r u))
    goal.before hsNorth hfSouth
  have hpre' : Relation.ReflTransGen (dock r).SourceStep (dock r).compile.initial s :=
    Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ hpre
  have hwhole := (Relation.ReflTransGen.single hm).trans hrest
  have hentry := (dock r).entry_hole_source hwhole goal.entry_empty
  have hreaderPre : Relation.ReflTransGen
      (NorthStep (wideReader r).compile.board none (wideReader r).width (wideReader r).targetLevel)
      (wideReader r).initialState.toState (readerState r s) :=
    (dock r).sourceState_prefix_keeping hpre hentry
  have hreaderStep : Step (wideReader r).compile.board none (readerState r s) (readerState r t) :=
    (dock r).sourceState_step hpre' hm ((dock r).entry_hole_source hrest goal.entry_empty)
  have hreaderSuffix : Reachable (wideReader r).compile.board none
      (readerState r t) (readerState r goal.state) :=
    (dock r).sourceState_between (hpre'.tail hm) hrest goal.entry_empty
  have htSouth' : (readerState r t).player.1.val < (wideReader r).width ∧
      (wideReader r).targetLevel ≤ (readerState r t).player.2.val := by
    by_contra h
    apply htSouth
    intro hx
    omega
  have hfx : (readerState r goal.state).player.1.val = 0 := congrArg (fun q => q.1.val) hgoal
  have hfy : (readerState r goal.state).player.2.val = (wideReader r).targetLevel :=
    congrArg (fun q => q.2.val) hgoal
  have hlanding := (wideReader r).first_south_landing hreaderPre hreaderStep htSouth' hreaderSuffix hfx hfy.ge
  exact ⟨⟨s, goal.state, hpre', hwhole, goal.after, hgoal, goal.entry_empty, hreaderPre, hlanding⟩⟩

end PushPuzzle.Push.Cyclic
