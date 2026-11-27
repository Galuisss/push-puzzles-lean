/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicInventory
public import Push.CyclicRows
public import PushFS.WallCongruence

/-! Recover an exact physical dock observation from a next-reader source corner trace. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

/-- An observed next-source state, its actual unturned dock state, and the same complete trajectory. -/
structure Observation (r : ColumnScan.Input)
    (observed : State (nextSource r).width (nextSource r).height) where
  state : State (dock r).outputWidth (dock r).outputHeight
  reachable : Reachable (dock r).compile.board none (dock r).compile.initial state
  player : state.player = (dock r).target
  turned : (turnGeometry (dock r).outputWidth (dock r).outputHeight).state state = observed

/-- A next-source corner computation has one exact unturned physical dock computation. -/
theorem observe_nextSource (r : ColumnScan.Input)
    {t : State (nextSource r).width (nextSource r).height}
    (hr : Reachable (nextSource r).board none (nextSource r).initial t)
    (ht : t.player = (nextSource r).target) : Nonempty (Observation r t) := by
  let I := (dock r).compile
  let e := turnGeometry I.width I.height
  have hnext' : Reachable (e.board I.board) none (e.state I.initial) t := by
    have h1 : Reachable (e.board I.board) none (nextSource r).initial t :=
      hr.reboard (by
        simp only [GridIsometry.board, Push.Instance.board, Push.Instance.toStorage, Finset.map_empty]
        rfl)
    have hinit : (nextSource r).initial = e.state I.initial := by
      simp only [nextSource, turn, Push.Instance.reflectedX, Push.Instance.transposed,
        Push.Instance.reorient, GridIsometry.state_trans]
      rfl
    rwa [hinit] at h1
  have hback := e.symm.reachable hnext'
  simp only [GridIsometry.board_symm, GridIsometry.state_symm] at hback
  have htarget : t.player = e.cells I.target := ht
  refine ⟨⟨e.symm.state t, hback, ?_, ?_⟩⟩
  · exact (congrArg e.cells.symm htarget).trans (e.cells.symm_apply_apply I.target)
  · exact e.symm.state_symm t

/-- A next-reader corner computation corresponds to one exact unturned physical dock computation. -/
theorem observe_nextInput (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (hb : rows.sum ≤ r.sourceHoles)
    {t : State (nextSource r).width (nextSource r).height}
    (hr : Reachable (nextInput r rows hlen hb).sourceBoard none
      (nextInput r rows hlen hb).initial.toState t)
    (ht : t.player = (nextInput r rows hlen hb).sourceCorner) : Nonempty (Observation r t) := by
  apply observe_nextSource r
  · have hnext := hr.reboard (B' := (nextSource r).board) rfl
    rwa [nextInput_initial] at hnext
  · exact ht.trans (nextInput_corner r rows hlen hb)

end PushPuzzle.Push.Cyclic
