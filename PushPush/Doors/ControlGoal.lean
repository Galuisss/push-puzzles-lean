/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ControlSource
public import PushPush.Doors.StockGeometry
import Mathlib.Tactic.FinCases

/-! The exact erasure target distinguishes accepted source executions. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors

theorem Layout.wirePath_private_x (L : Layout) (index : Fin L.wires.length)
    (wire : Wire) (corner : Fin 8) (hzero : corner ≠ 0) (hseven : corner ≠ 7) :
    ((L.wirePath index.val wire).getD corner.val (0, 0)).1 + 2 < L.rackX := by
  have hi := index.isLt
  fin_cases corner <;>
    simp_all [Layout.wirePath, Layout.wireA, Layout.wireB, Layout.wireC, Layout.rackX] <;> omega

namespace Source

theorem SignalPosition.wire_ne_erase (storage : Bool) (I : Instance)
    (index : Fin (layout storage I).wires.length) (corner : Fin 8)
    (door : Fin I.doors.length)
    (htarget : (layout storage I).wires[index].target ≠ doorBase door.val + 70) :
    (SignalPosition.wire index corner).point ≠
      ((layout storage I).rackX - 1, doorBase door.val + 70 + (layout storage I).shift) := by
  by_cases hzero : corner = 0
  · subst corner
    rw [SignalPosition.point_wire_start]
    intro he
    have hy := congrArg Prod.snd he
    change (layout storage I).wires[index].source + (layout storage I).shift =
      doorBase door.val + 70 + (layout storage I).shift at hy
    have hrow : (layout storage I).wires[index].source = doorBase door.val + 70 := by omega
    apply door_register_not_launch I door Register.erase
    have hl : LaunchRow I (layout storage I).wires[index].source :=
      wires_launch storage I (List.getElem_mem index.isLt)
    simpa only [hrow, Register.row] using hl
  · by_cases hseven : corner = 7
    · subst corner
      rw [SignalPosition.point_wire_end]
      intro he
      have hy := congrArg Prod.snd he
      change (layout storage I).wires[index].target + (layout storage I).shift =
        doorBase door.val + 70 + (layout storage I).shift at hy
      exact htarget (by omega)
    · intro he
      have hx := congrArg Prod.fst he
      have hprivate := Layout.wirePath_private_x (layout storage I) index
        (layout storage I).wires[index] corner hzero hseven
      change (SignalPosition.wire index corner).point.1 + 2 < (layout storage I).rackX at hprivate
      rw [he] at hprivate
      dsimp at hprivate
      omega

private theorem ControlPhase.signal_ne_erase {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C)
    (door : Fin I.doors.length) :
    C.signal.point ≠ ((layout storage I).rackX - 1,
      doorBase door.val + 70 + (layout storage I).shift) := by
  cases hphase with
  | junction j p hj hp =>
    intro he
    have hy := congrArg Prod.snd he
    change inputRow I (rank I source.location) j p + (layout storage I).shift =
      doorBase door.val + 70 + (layout storage I).shift at hy
    exact inputRow_ne_door_register I (rank I source.location) j p door Register.erase
      (Nat.add_right_cancel hy)
  | upper j hj hused =>
    intro he
    have hy := congrArg Prod.snd he
    change upperRow I (rank I source.location) j + (layout storage I).shift =
      doorBase door.val + 70 + (layout storage I).shift at hy
    exact upperRow_ne_door_register I (rank I source.location) j door Register.erase
      (Nat.add_right_cancel hy)
  | lower j hj hused =>
    intro he
    have hy := congrArg Prod.snd he
    change lowerRow I (rank I source.location) j + (layout storage I).shift =
      doorBase door.val + 70 + (layout storage I).shift at hy
    exact lowerRow_ne_door_register I (rank I source.location) j door Register.erase
      (Nat.add_right_cancel hy)
  | junctionWire index corner j p hj hp htarget =>
    apply SignalPosition.wire_ne_erase storage I index corner door
    rw [htarget]
    exact inputRow_ne_door_register I _ _ _ door Register.erase
  | call active channel stored incoming hentry hsession =>
    intro he
    have hy := congrArg Prod.snd he
    change doorBase active.val + incoming.row + (layout storage I).shift =
      doorBase door.val + 70 + (layout storage I).shift at hy
    have hr := door_register_injective I active door (Register.ofSlot incoming) Register.erase
      (by simpa only [Register.row_ofSlot, (show Register.erase.row = 70 from rfl)] using
        Nat.add_right_cancel hy)
    exact ofSlot_ne_erase incoming hr.2
  | result active channel stored incoming keep hentry hsession =>
    intro he
    have hy := congrArg Prod.snd he
    cases keep
    · change doorBase active.val + Room.landing incoming stored + (layout storage I).shift =
        doorBase door.val + 70 + (layout storage I).shift at hy
      exact result_ne_door_register I active door incoming stored Register.erase
        (Nat.add_right_cancel hy)
    · change doorBase active.val + Room.landing stored incoming + (layout storage I).shift =
        doorBase door.val + 70 + (layout storage I).shift at hy
      exact result_ne_door_register I active door stored incoming Register.erase
        (Nat.add_right_cancel hy)
  | doorWire active channel stored incoming index corner hentry hsession htarget =>
    apply SignalPosition.wire_ne_erase storage I index corner door
    rw [htarget]
    intro he
    have hr := door_register_injective I active door (Register.ofSlot incoming) Register.erase
      (by simpa only [Register.row_ofSlot, (show Register.erase.row = 70 from rfl)] using he)
    exact ofSlot_ne_erase incoming hr.2

/-- Before source acceptance, no physical door-erasure cell contains a mobile box. -/
theorem ControlPhase.erasePoint_empty {I : Instance} {source : State} {C : Control true I}
    (hphase : ControlPhase true I source C) (door : Fin I.doors.length) :
    doorCell true I door 70 (by omega) ∉ C.stock.boxes true := by
  intro hp
  have hp := ((layout true I).mem_raster _ _).mp hp
  change ((layout true I).rackX - 1, doorBase door.val + 70 + (layout true I).shift) ∈
    C.stock.rawBoxes true at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · exact fixed_door_clear true I door (doorCell true I door 70 (by omega)) rfl
        (by dsimp [doorCell, workCell, Layout.point]; omega)
        (by dsimp [doorCell, workCell, Layout.point]; omega) hp
    · obtain ⟨i, _, he⟩ := Finset.mem_image.mp hp
      have hi := Register.row_bounds (C.register i)
      have hy := congrArg Prod.snd he
      change doorBase i.val + (C.register i).row + (layout true I).shift =
        doorBase door.val + 70 + (layout true I).shift at hy
      have hid := door_register_injective I i door (C.register i) Register.erase
        (Nat.add_right_cancel hy)
      exact hphase.register_ne_erase i hid.2
  · exact hphase.signal_ne_erase door (Finset.mem_singleton.mp hp).symm

private theorem erasePoint_goal_mem (I : Instance) (door : Fin I.doors.length) :
    doorCell true I door 70 (by omega) ∈ (puzzle true I).board.goals := by
  apply ((layout true I).mem_raster _ _).mpr
  apply Finset.mem_union_right
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨doorBase door.val + 70, List.mem_cons_of_mem _ ?_, rfl⟩
  exact List.mem_map.mpr ⟨door.val, List.mem_range.mpr door.isLt, rfl⟩

/-- Any safe control stock solving a nonempty storage network has reached its original target. -/
theorem Control.SourceSafe.source_of_goals_nonempty {I : Instance} (hdoors : 0 < I.doors.length)
    {C : Control true I} (hsafe : C.SourceSafe)
    (hgoal : C.stock.boxes true = (puzzle true I).board.goals) :
    I ∈ Cslib.Complexity.SelfClosingDoor.Reachability := by
  rcases hsafe with haccept | ⟨source, hreach, hphase⟩
  · exact haccept
  · let door : Fin I.doors.length := ⟨0, hdoors⟩
    exact False.elim (hphase.erasePoint_empty door (hgoal ▸ erasePoint_goal_mem I door))

end Source
end PushPuzzle.PushPush.Doors
