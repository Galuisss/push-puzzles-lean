/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutNeighbor
public import PushPush.Doors.WireReadoutRepair

/-! Same-sign B/C faults permit one attraction before entering a dead stock. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

/-- The actual four-box configuration created by a same-sign reverse-pin push. -/
structure ExtendedFault (storage : Bool) (I : Instance) (S : Stock I) where
  normal : Direction
  forward : Direction
  signal : Cell (layout storage I).width (layout storage I).height
  near : Cell (layout storage I).width (layout storage I).height
  extra : Cell (layout storage I).width (layout storage I).height
  removed : Cell (layout storage I).width (layout storage I).height
  remote : Cell (layout storage I).width (layout storage I).height
  normalCorner : Wire.Corner normal signal extra removed
  nearAdj : Adjacent normal signal near
  extendedCorner : Wire.Corner forward near signal remote
  extraAdj : Adjacent forward.opposite signal extra
  extra_pin : (extra.1.val, extra.2.val) ∈ (layout storage I).pins
  removed_pin : (removed.1.val, removed.2.val) ∈ (layout storage I).pins
  remote_pin : (remote.1.val, remote.2.val) ∈ (layout storage I).pins
  signal_raw : (signal.1.val, signal.2.val) = S.signal
  signal_private : signal.1.val < (layout storage I).rackX - 1
  near_margin : near.1.val + 1 < (layout storage I).rackX - 1
  remote_ne_removed : remote ≠ removed
  removed_ne_near : removed ≠ near
  horizontal : forward = .east ∨ forward = .west
  free_near : ∀ landed : Cell (layout storage I).width (layout storage I).height,
    Adjacent forward near landed → ∀ p ∈ (layout storage I).pins, p.1 ≠ landed.1.val
  free_remote : ∀ landed : Cell (layout storage I).width (layout storage I).height,
    Adjacent forward landed remote → ∀ p ∈ (layout storage I).pins, p.1 ≠ landed.1.val

end PushPuzzle.PushPush.Doors.Source
