/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.TerminalInventory

/-! A restored terminal frame freezes the same frame along every successful prefix. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction)

structure RestoredFrame (storage : Bool) (I : Instance)
    (final : PushFS.State (layout storage I).width (layout storage I).height) : Prop where
  interior : Interior final
  rack : line .south (layout storage I).rackX final.boxes =
    line .south (layout storage I).rackX (puzzle storage I).initial.boxes
  dividers : ∀ g ∈ (layout storage I).dividers,
    ∀ p : Cell (layout storage I).width (layout storage I).height,
      p.1.val = (layout storage I).rackX - 1 → p.2.val = g + (layout storage I).shift →
        VerticallyIsolated final p
  caps : ∀ y ∈ (layout storage I).caps,
    ∀ p : Cell (layout storage I).width (layout storage I).height,
      p.1.val = (layout storage I).rackX - 1 → p.2.val = y + (layout storage I).shift → p ∈ final.boxes

private theorem RestoredFrame.prefix {storage : Bool} {I : Instance}
    {s final : PushFS.State (layout storage I).width (layout storage I).height}
    (H : RestoredFrame storage I final)
    (hprefix : Reachable (puzzle storage I).initial s) (hsuffix : Reachable s final) :
    Protected storage I s where
  interior := hsuffix.interior_source H.interior
  supported := hprefix.supported (hsuffix.interior_source H.interior) (initial_supported storage I)
  rack := hprefix.rack_frozen hsuffix (initial_supported storage I) H.interior H.rack
  dividers := by
    intro g hg p hx hy
    exact hprefix.divider_frozen hsuffix (initial_supported storage I) H.interior H.rack
      (divider_guard storage I hg p hx hy) (H.dividers g hg p hx hy)
  caps := by
    intro y hy q hqx hqy
    obtain ⟨g, hg, p, hpx, hpy, hguard⟩ := cap_guard storage I hy q hqx hqy
    exact hprefix.cap_frozen hsuffix (initial_supported storage I) H.interior H.rack
      hguard (H.dividers g hg p hpx hpy) (H.caps y hy q hqx hqy)

theorem RestoredFrame.corridor {storage : Bool} {I : Instance}
    {final : PushFS.State (layout storage I).width (layout storage I).height}
    (H : RestoredFrame storage I final) :
    ProtectedCorridor storage I (puzzle storage I).initial final :=
  fun _ hp hs => H.prefix hp hs

end PushPuzzle.PushPush.Doors.Source
