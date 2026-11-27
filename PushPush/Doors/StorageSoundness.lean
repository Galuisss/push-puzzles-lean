/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.PhysicalDecoder

/-! Every actual exact-storage solution decodes to the original door-network reachability. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity

private theorem successfulPushDecoder (I : Instance) : SuccessfulPushDecoder I :=
  ⟨fun M hp => M.pin_readout hp, fun M hs => M.signal_readout hs⟩

theorem physical_storage_sound (I : Instance)
    {final : PushFS.State (layout true I).width (layout true I).height}
    (hactual : Reachable (puzzle true I).initial final)
    (hgoals : final.boxes = (puzzle true I).board.goals) : I ∈ SelfClosingDoor.Reachability :=
  (successfulPushDecoder I).sound hactual hgoals

end PushPuzzle.PushPush.Doors.Source
