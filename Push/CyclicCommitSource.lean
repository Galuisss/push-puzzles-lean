/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicCommit
public import Push.ColumnScanSoundness

/-! The exact original source state and paid quotas at the same physical cyclic commitment. -/

@[expose] public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

/-- Original source cells before the cyclic quarter turn. -/
def unturnedSourceEmbed (r : ColumnScan.Input) (q : Cell r.width r.height) :
    Cell (dock r).outputWidth (dock r).outputHeight := (dock r).embed ((wideReader r).embed q)

/-- Original source-column holes in any physical dock state. -/
def sourceColumn (r : ColumnScan.Input) (i : Fin r.width)
    (s : State (dock r).outputWidth (dock r).outputHeight) :
    Finset (Cell (dock r).outputWidth (dock r).outputHeight) :=
  (holes s).filter fun q => q.1.val = i.val + 2 ∧ q.2.val < r.height

private theorem reader_column_card (r : ColumnScan.Input) (i : Fin r.width)
    (s : State (dock r).outputWidth (dock r).outputHeight) :
    (ReadBudgetProjection.sourceCells i.val r.height (readerState r s)).card = (sourceColumn r i s).card := by
  apply (dock r).sourceState_column_card
  · have := i.isLt
    change i.val < r.width + 2 + (r.width + 1 + r.extraWidth)
    omega
  · change r.height ≤ r.height + (wideReader r).length
    omega

namespace Commit

variable {r : ColumnScan.Input} {finish : State (dock r).outputWidth (dock r).outputHeight}
  (c : Commit r finish)

/-- The original live source bitmap at this actual physical commitment. -/
def sourceState : State r.width r.height := (wideReader r).cropState (readerState r c.state)

theorem source_reachable : Reachable r.sourceBoard none r.initial.toState c.sourceState := by
  have hfx : (readerState r c.readerEnd).player.1.val = 0 := congrArg (fun q => q.1.val) c.readerGoal
  have hfy : (readerState r c.readerEnd).player.2.val = (wideReader r).targetLevel :=
    congrArg (fun q => q.2.val) c.readerGoal
  exact (wideReader r).before_south_source_reachable c.readerBefore c.readerSuffix hfx hfy.ge

theorem source_player : c.sourceState.player = r.sourceCorner := by
  have hfx : (readerState r c.readerEnd).player.1.val = 0 := congrArg (fun q => q.1.val) c.readerGoal
  have hfy : (readerState r c.readerEnd).player.2.val = (wideReader r).targetLevel :=
    congrArg (fun q => q.2.val) c.readerGoal
  exact ((wideReader r).landing_source_prefix c.readerBefore c.readerSuffix hfx hfy.ge c.readerLanding).2.1

/-- The recovered source and the real dock commitment have exactly the same original holes. -/
theorem source_hole (q : Cell r.width r.height) :
    q ∈ holes c.sourceState ↔ unturnedSourceEmbed r q ∈ holes c.state :=
  ((wideReader r).cropState_mem_holes (readerState r c.state) q).trans
    ((dock r).sourceState_hole c.state ((wideReader r).embed q))

theorem source_holes_card : (holes c.sourceState).card = r.sourceHoles := by
  rw [card_holes_reachable c.source_reachable, r.initial.holes_toState]
  rfl

theorem source_column_card (i : Fin r.width) : (sourceColumn r i c.state).card =
    ((holes c.sourceState).filter fun q => q.1 = i).card :=
  (reader_column_card r i c.state).symm.trans
    ((wideReader r).crop_column_card (readerState r c.state) i)

/-- Before entering the dock, the actual reader has already consumed every source-column quota. -/
theorem reader_consumed_quotas : ∀ i : Fin r.width,
    r.quotas.getD i.val 0 + (sourceColumn r i c.readerEnd).card ≤ (sourceColumn r i c.state).card := by
  intro i
  have hfx : (readerState r c.readerEnd).player.1.val = 0 := congrArg (fun q => q.1.val) c.readerGoal
  have hfy : (readerState r c.readerEnd).player.2.val = (wideReader r).targetLevel :=
    congrArg (fun q => q.2.val) c.readerGoal
  have hb := (wideReader r).landing_column_consumed_quotas c.readerBefore c.readerSuffix hfx hfy c.readerLanding i
  change r.quotas.getD i.val 0 +
    (ReadBudgetProjection.sourceCells i.val r.height (readerState r c.readerEnd)).card ≤
      (ReadBudgetProjection.sourceCells i.val r.height (readerState r c.state)).card at hb
  rwa [reader_column_card r i c.readerEnd, reader_column_card r i c.state] at hb

end Commit
end PushPuzzle.Push.Cyclic
