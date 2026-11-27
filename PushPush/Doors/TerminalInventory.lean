/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ProtectedFrame
public import PushPush.Doors.WireDeadlock

/-! The two terminal inventory facts needed to reject every private dead stock. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell)

/-- A successful terminal inventory restores the pins and has no additional private box. -/
structure TerminalInventory (storage : Bool) (I : Instance)
    (boxes : Finset (Cell (layout storage I).width (layout storage I).height)) : Prop where
  pins : ∀ p : Cell (layout storage I).width (layout storage I).height,
    (p.1.val, p.2.val) ∈ (layout storage I).pins → p ∈ boxes
  private_pin : ∀ p ∈ boxes, p.1.val < (layout storage I).rackX - 1 →
    (p.1.val, p.2.val) ∈ (layout storage I).pins

/-- Only protected states occur between these two states of the same successful path. -/
def ProtectedCorridor (storage : Bool) (I : Instance)
    (start final : PushFS.State (layout storage I).width (layout storage I).height) : Prop :=
  ∀ state, Reachable start state → Reachable state final → Protected storage I state

theorem ProtectedCorridor.tail {storage : Bool} {I : Instance}
    {start middle final : PushFS.State (layout storage I).width (layout storage I).height}
    (hc : ProtectedCorridor storage I start final) (hm : Reachable start middle) :
    ProtectedCorridor storage I middle final :=
  fun state hms hsf => hc state (hm.trans hms) hsf

theorem TerminalInventory.goals (storage : Bool) (I : Instance) :
    TerminalInventory storage I (puzzle storage I).board.goals := by
  constructor
  · intro p hp
    apply ((layout storage I).mem_raster _ _).mpr
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hp))
  · intro p hp hx
    have hp := ((layout storage I).mem_raster _ _).mp hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_union.mp hp with hp | hp
        · exact hp
        · have hc := (layout storage I).rack_column hp
          omega
      · have hc := (layout storage I).blockers_column hp
        omega
    · obtain ⟨row, _, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
      have hc := congrArg Prod.fst he
      dsimp at hc
      omega

/-- Any restored missing pin excludes a permanently dead source inventory. -/
theorem deadStock_reject_inventory {storage : Bool} {I : Instance}
    {s final : PushFS.State (layout storage I).width (layout storage I).height}
    (hsuffix : Reachable s final) (hprotected : ProtectedCorridor storage I s final)
    (hterminal : TerminalInventory storage I final.boxes)
    (hd : Wire.DeadStock s.boxes (Protected storage I))
    (missing : Cell (layout storage I).width (layout storage I).height)
    (hpin : (missing.1.val, missing.2.val) ∈ (layout storage I).pins)
    (hmissing : missing ∉ s.boxes) : False := by
  have hb := hd.reachable_boxes rfl hsuffix hprotected
  exact hmissing (hb ▸ hterminal.pins missing hpin)

end PushPuzzle.PushPush.Doors.Source
