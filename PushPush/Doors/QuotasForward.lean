/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasAccept
public import PushPush.Doors.QuotasPolyTime
public import PushPush.Doors.ForwardPhysical
public import PushPush.Basic
public import Push.SourceGame

/-! Actual source computations park and pay the complete polynomial-time seven-round reader. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity Turing.MultiTapeTM
open Push.AcceptanceProgram

/-- The unchanged door work board with the real southeast player destination. -/
def readerSource (I : Instance) : PushPush.Instance := Push.SourceGame.ofStorage (puzzle false I)

/-- The seven actual full-quota rounds emitted from the same work board. -/
def readerRounds (I : Instance) : List Round := (layout false I).quotaProgram.rounds

@[fun_prop] theorem readerSource_polyTime :
    ComputableInPolyTime readerSource SelfClosingDoor.encInstance PushPush.encoding :=
  Push.SourceGame.ofStorage_polyTime.comp (puzzle_polyTime false)

@[fun_prop] theorem readerRounds_polyTime :
    ComputableInPolyTime readerRounds SelfClosingDoor.encInstance encRounds :=
  Layout.quotaProgram_rounds_polyTime.comp (layout_polyTime false)

theorem readerSource_target (I : Instance) : (readerSource I).target = (layout false I).corner := rfl

/-- The original explicit rectangle has exactly the full seven-round payment budget. -/
theorem readerRounds_budget (I : Instance) :
    Push.Scan.quota (instructions (w := (readerSource I).width) (h := (readerSource I).height) (readerRounds I)) =
      ((readerSource I).initial.boxesᶜ).card :=
  (layout_balanced false I).quotaProgram_initial

/-- Every positive source network parks its complete register stock at the accepting output. -/
theorem reaches_parked (I : Instance) (hs : I ∈ SelfClosingDoor.Reachability) :
    ∃ S : Stock I, Reachable (readerSource I).initial (S.canonical false) ∧
      S.signal = atRow false I (layout false I).stop := by
  obtain ⟨s, port, ht, hp, hr⟩ := physical_reaches_target false I hs
  let current := encodedState false I s port
  have hused : upperUsed I (rank I I.target) 0 = true := by simp [upperUsed]
  have hsignal : current.signal = atRow false I (inputRow I (rank I I.target) 0 port) := by
    simp only [current, encodedState, Stock.ofBits, ht]
  have hpark := current.junction_upper false (rank I I.target) 0 port
    (rank_bound I (target_mem I)) (slots_pos I) hp hused hsignal
  let parked : Stock I := {current with signal := atRow false I (layout false I).stop}
  have hpark' : Reachable (current.canonical false) (parked.canonical false) := hpark
  exact ⟨parked, hr.trans hpark', rfl⟩

end PushPuzzle.PushPush.Doors.Source
