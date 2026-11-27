/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.SourceFamily
public import PushPush.Doors.QuotasTerminalColumns
public import PushPush.Doors.QuotasTerminalReadout

/-! The complete seven-round whole-run source language reads precisely source-network reachability. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity

private theorem BlocksAccepted.sound {I : Instance}
    (H : BlocksAccepted I) : I ∈ SelfClosingDoor.Reachability := by
  obtain ⟨t, hr, _, H⟩ := H.exact
  obtain ⟨W⟩ := reader_neighbor_witness I H
  obtain ⟨hframe, _⟩ := reader_frame_parked I hr H
  have hcolumns := W.private_columns (readerRounds_frame I t.boxesᶜ ⟨∅, H.eval⟩)
    (hr.supported hframe.interior (initial_supported false I)) hframe.rack rfl
  exact (reader_terminal_of_exec I hr H hcolumns).sound hr

theorem blocksAccepted_iff (I : Instance) : BlocksAccepted I ↔ I ∈ SelfClosingDoor.Reachability :=
  ⟨BlocksAccepted.sound, blocksAccepted_of_mem I⟩

theorem sourceFamily_language_iff_reachability (I : Instance) :
    CyclicReader.SourceLanguage sourceFamily I ↔ I ∈ SelfClosingDoor.Reachability :=
  (sourceFamily_language_iff I).trans (blocksAccepted_iff I)

end PushPuzzle.PushPush.Doors.Source
