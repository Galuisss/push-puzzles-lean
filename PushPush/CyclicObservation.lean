/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Isometry
public import Push.CyclicObservation

/-! Unturn an actual maximum-sliding next-reader computation. -/

@[expose] public section
namespace PushPuzzle.PushPush.Cyclic

open PushFS (State)
open Push.Cyclic

structure Observation (r : Push.ColumnScan.Input)
    (observed : State (nextSource r).width (nextSource r).height) where
  state : State (dock r).outputWidth (dock r).outputHeight
  reachable : Reachable (dock r).compile.initial state
  player : state.player = (dock r).target
  turned : (turnGeometry (dock r).outputWidth (dock r).outputHeight).state state = observed

private theorem observe_nextSource (r : Push.ColumnScan.Input)
    {t : State (nextSource r).width (nextSource r).height}
    (hr : Reachable (nextSource r).initial t) (ht : t.player = (nextSource r).target) :
    Nonempty (Observation r t) := by
  let e := turnGeometry (dock r).outputWidth (dock r).outputHeight
  have hi : (nextSource r).initial = e.state (dock r).compile.initial := by
    exact PushFS.GridIsometry.state_trans _ _ _
  rw [hi] at hr
  have hback := Reachable.reorient hr e.symm
  have hback' : Reachable (dock r).compile.initial (e.symm.state t) :=
    Eq.mp (congrArg (fun u => Reachable u (e.symm.state t))
      (e.state_symm (dock r).compile.initial)) hback
  refine ⟨⟨e.symm.state t, hback', ?_, e.symm.state_symm t⟩⟩
  have hp : t.player = e.cells (dock r).target := ht
  exact (congrArg e.cells.symm hp).trans (e.cells.symm_apply_apply _)

theorem observe_nextInput (r : Push.ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (hb : rows.sum ≤ r.sourceHoles)
    {t : State (nextSource r).width (nextSource r).height}
    (hr : Reachable (nextInput r rows hlen hb).initial.toState t)
    (ht : t.player = (nextInput r rows hlen hb).sourceCorner) : Nonempty (Observation r t) := by
  apply observe_nextSource r
  · rwa [nextInput_initial] at hr
  · exact ht.trans (nextInput_corner r rows hlen hb)

theorem turn_nextInput (r : Push.ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (hb : rows.sum ≤ r.sourceHoles)
    {s : State (dock r).outputWidth (dock r).outputHeight}
    (hr : Reachable (dock r).compile.initial s) (hp : s.player = (dock r).target) :
    Reachable (nextInput r rows hlen hb).initial.toState
      ((turnGeometry (dock r).outputWidth (dock r).outputHeight).state s) ∧
    ((turnGeometry (dock r).outputWidth (dock r).outputHeight).state s).player =
      (nextInput r rows hlen hb).sourceCorner := by
  let e := turnGeometry (dock r).outputWidth (dock r).outputHeight
  have hi : e.state (dock r).compile.initial = (nextSource r).initial :=
    (PushFS.GridIsometry.state_trans _ _ _).symm
  have hreach : Reachable (nextSource r).initial (e.state s) :=
    Eq.mp (congrArg (fun u => Reachable u (e.state s)) hi) (Reachable.reorient hr e)
  refine ⟨?_, (congrArg e.cells hp).trans (nextInput_corner r rows hlen hb).symm⟩
  exact Eq.mpr (congrArg (fun u => Reachable u (e.state s)) (nextInput_initial r rows hlen hb)) hreach

end PushPuzzle.PushPush.Cyclic
