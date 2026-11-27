/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ColumnDecoder

/-! Complete source soundness from protected execution and private-column reader budgets. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity

private theorem columnPushDecoder (storage : Bool) (I : Instance)
    (initial final : PushFS.State (layout storage I).width (layout storage I).height)
    (hterminal : PrivateColumnInventory storage I final.boxes) :
    ProtectedPushDecoder storage I initial final :=
  ⟨fun M hp => M.pin_readout_columns hterminal hp,
    fun M hs => M.signal_readout_columns hterminal hs⟩

theorem physical_columns_sound (storage : Bool) (I : Instance)
    {initial final : PushFS.State (layout storage I).width (layout storage I).height}
    (hcorridor : ProtectedCorridor storage I initial final)
    (hterminal : PrivateColumnInventory storage I final.boxes)
    (hinitial : (Control.initial storage I).stock.Realizes storage initial)
    (hactual : Reachable initial final)
    (hpark : workCell storage I (targetRow I) (targetRow_fit storage I) ∈ final.boxes) :
    I ∈ SelfClosingDoor.Reachability :=
  (columnPushDecoder storage I initial final hterminal).sound hcorridor hinitial hactual hpark

end PushPuzzle.PushPush.Doors.Source
