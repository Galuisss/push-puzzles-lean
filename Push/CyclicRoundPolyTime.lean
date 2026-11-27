/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicRoundStep
public import Push.CyclicReaderBasePolyTime
public import Push.AcceptanceProgramPolyTimeSets

/-! Standard machine PT for complete compact read/clear source transport. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS AcceptanceProgram Turing.MultiTapeTM
open scoped PushPuzzle.Push.AcceptanceProgram

/-- The complete compact source-embedding block emits in standard polynomial time. -/
@[fun_prop] theorem sourceRound_polyTime : ComputableInPolyTime sourceRound encRound encRound := by
  have hc : ComputableInPolyTime
      (fun p : Unit × Direction × Finset ℕ => (p.2.2).image (sourceLane p.2.1))
      (encPair encUnit (encPair (encFinite Direction) encLaneSet)) encLaneSet := by
    apply laneSet_image_polyTime (by fun_prop)
    fun_prop
  have h := encRound_elim_polyTime (encP := encUnit) (encE := encRound)
    (g0 := fun p => .read p.2.1 (sourceRequests p.2.1 p.2.2))
    (g1 := fun p => .clear p.2.1 (p.2.2.image (sourceLane p.2.1))) (by fun_prop) (by fun_prop)
  have hh := h.comp (show ComputableInPolyTime (fun block : Round => ((), block))
    encRound (encPair encUnit encRound) from by fun_prop)
  exact hh.of_enc_eq (by intro block; cases block <;> rfl)

/-- Actual turning of both read requests and clear sets emits in standard polynomial time. -/
@[fun_prop] theorem turnRound_polyTime : ComputableInPolyTime
    (fun p : ℕ × Round => turnRound p.1 p.2) (encPair encUnary encRound) encRound := by
  have hs : ComputableInPolyTime turnSide (encFinite Direction) (encFinite Direction) := .of_finite _
  have hc : ComputableInPolyTime
      (fun p : ℕ × Direction × Finset ℕ => turnLanes p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair (encFinite Direction) encLaneSet)) encLaneSet := by
    unfold turnLanes
    apply laneSet_image_polyTime (by fun_prop)
    fun_prop
  have h := encRound_elim_polyTime (encP := encUnary) (encE := encRound)
    (g0 := fun p => .read (turnSide p.2.1) (turnRequests p.1 p.2.1 p.2.2))
    (g1 := fun p => .clear (turnSide p.2.1) (turnLanes p.1 p.2.1 p.2.2)) (by fun_prop) (by fun_prop)
  exact h.of_enc_eq (by intro p; rcases p with ⟨_, block⟩; cases block <;> rfl)

private theorem dock_width_polyTime : ComputableInPolyTime
    (fun r => (dock r).outputWidth) ColumnScan.Input.encoding encUnary :=
  PushFS.Machine.width_polyTime.comp
    (Push.Machine.toStorage_polyTime.comp (CornerDock.Input.compile_polyTime.comp dock_polyTime))

/-- The complete future program uses only actual polynomial-time lane translations and turns. -/
@[fun_prop] theorem nextRounds_polyTime {α : Type} {enc : α ↪ List Bool}
    {reader : α → ColumnScan.Input} {rounds : α → List Round}
    (hr : ComputableInPolyTime reader enc ColumnScan.Input.encoding)
    (hb : ComputableInPolyTime rounds enc encRounds) :
    ComputableInPolyTime (fun a => nextRounds (reader a) (rounds a)) enc encRounds := by
  have hw := dock_width_polyTime.comp hr
  unfold nextRounds encRounds
  apply ComputableInPolyTime.mapWithInput hb
  exact turnRound_polyTime.comp ((hw.comp (ComputableInPolyTime.fst enc encRound)).prod
    (sourceRound_polyTime.comp (ComputableInPolyTime.snd enc encRound)))

end PushPuzzle.Push.Cyclic
