/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.PhysicalState
public import PushPush.Doors.ForwardControl

/-! A parked signal witnesses source acceptance independently of the final door bits. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity

private theorem Stock.signal_of_parked (storage : Bool) (I : Instance) (S : Stock I)
    (hpark : workCell storage I (targetRow I) (targetRow_fit storage I) ∈ S.boxes storage) :
    S.signal = atRow storage I (targetRow I) := by
  have hp := ((layout storage I).mem_raster _ _).mp hpark
  change ((layout storage I).rackX - 1, targetRow I + (layout storage I).shift) ∈ S.rawBoxes storage at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨row, hrow, he⟩ := ((layout storage I).fixed_working_iff _).mp hp
      have hroweq : row = targetRow I := by omega
      exact False.elim (targetRow_free storage I (hroweq ▸ hrow))
    · have hbefore := S.registerPoint_before storage hp
      have htarget := targetRow_lower_bound I
      dsimp at hbefore
      omega
  · exact (Finset.mem_singleton.mp hp).symm

private theorem ControlPhase.location_of_parked {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C)
    (hregular : C.signal.Regular) (hlabel : source.location ∈ labels I)
    (hpoint : C.signal.point = atRow storage I (targetRow I)) : source.location = I.target := by
  have hh := chamberHeight_ge I
  have ht := targetRow_lower_bound I
  cases hphase with
  | junction j p hj hp =>
    have hy := congrArg Prod.snd hpoint
    change inputRow I (rank I source.location) j p + (layout storage I).shift =
      targetRow I + (layout storage I).shift at hy
    have he : inputRow I (rank I source.location) j p = targetRow I := Nat.add_right_cancel hy
    have hl : LaunchRow I (targetRow I) := Or.inr ⟨rank I I.target, 0, Or.inl rfl⟩
    exact False.elim (inputRow_not_launch I _ _ _ hp (he.symm ▸ hl))
  | upper j hj hused =>
    have hy := congrArg Prod.snd hpoint
    change upperRow I (rank I source.location) j + (layout storage I).shift =
      targetRow I + (layout storage I).shift at hy
    have he : upperRow I (rank I source.location) j = targetRow I := Nat.add_right_cancel hy
    have hid := room_row_injective I hj (slots_pos I) (by omega : 3 < chamberHeight I)
      (by omega : 3 < chamberHeight I) he
    exact (rank_eq_iff I hlabel).mp hid.1
  | lower j hj hused =>
    have hy := congrArg Prod.snd hpoint
    change lowerRow I (rank I source.location) j + (layout storage I).shift =
      targetRow I + (layout storage I).shift at hy
    have he : lowerRow I (rank I source.location) j = targetRow I := Nat.add_right_cancel hy
    have he' : roomBase I (rank I source.location) j + (chamberHeight I - 3) =
        roomBase I (rank I I.target) 0 + 3 := by unfold lowerRow targetRow upperRow at he; omega
    have hid := room_row_injective I hj (slots_pos I) (by omega : chamberHeight I - 3 < chamberHeight I)
      (by omega : 3 < chamberHeight I) he'
    omega
  | junctionWire index corner j p hj hp htarget =>
    have hprivate := Layout.wirePath_private_x (layout storage I) index (layout storage I).wires[index]
      corner (by intro he; subst corner; exact Nat.lt_irrefl _ hregular.1)
      (by intro he; subst corner; exact Nat.lt_irrefl _ hregular.2)
    change (SignalPosition.wire index corner).point.1 + 2 < (layout storage I).rackX at hprivate
    rw [hpoint] at hprivate
    dsimp [atRow] at hprivate
    omega
  | call door channel stored incoming hentry hsession =>
    have hy := congrArg Prod.snd hpoint
    change doorBase door.val + incoming.row + (layout storage I).shift =
      targetRow I + (layout storage I).shift at hy
    have hrow := Room.slot_row_bounds incoming
    have hb := door_row_before I door.isLt (by omega : incoming.row < 90)
    omega
  | result door channel stored incoming keep hentry hsession =>
    have hy := congrArg Prod.snd hpoint
    cases keep
    · change doorBase door.val + Room.landing incoming stored + (layout storage I).shift =
        targetRow I + (layout storage I).shift at hy
      have hrow := landing_bounds incoming stored
      have hb := door_row_before I door.isLt (by omega : Room.landing incoming stored < 90)
      omega
    · change doorBase door.val + Room.landing stored incoming + (layout storage I).shift =
        targetRow I + (layout storage I).shift at hy
      have hrow := landing_bounds stored incoming
      have hb := door_row_before I door.isLt (by omega : Room.landing stored incoming < 90)
      omega
  | doorWire door channel stored incoming index corner hentry hsession htarget =>
    have hprivate := Layout.wirePath_private_x (layout storage I) index (layout storage I).wires[index]
      corner (by intro he; subst corner; exact Nat.lt_irrefl _ hregular.1)
      (by intro he; subst corner; exact Nat.lt_irrefl _ hregular.2)
    change (SignalPosition.wire index corner).point.1 + 2 < (layout storage I).rackX at hprivate
    rw [hpoint] at hprivate
    dsimp [atRow] at hprivate
    omega

private theorem Control.SourceSafe.source_of_parked {storage : Bool} {I : Instance}
    {C : Control storage I}
    (hsafe : C.SourceSafe) (hregular : C.signal.Regular)
    (hpoint : C.signal.point = atRow storage I (targetRow I)) :
    I ∈ SelfClosingDoor.Reachability := by
  rcases hsafe with haccept | ⟨source, hreach, hphase⟩
  · exact haccept
  · exact ⟨source, hreach, hphase.location_of_parked hregular (reachable_location_mem I hreach) hpoint⟩

/-- A physical parking box in any normalized control execution certifies original target reachability. -/
theorem Control.Reachable.source_of_parked {storage : Bool} {I : Instance} {C : Control storage I}
    (hr : Control.Reachable (Control.initial storage I) C) (hregular : C.signal.Regular)
    (hpark : workCell storage I (targetRow I) (targetRow_fit storage I) ∈ C.stock.boxes storage) :
    I ∈ SelfClosingDoor.Reachability := by
  exact hr.sourceSafe.source_of_parked hregular (Stock.signal_of_parked storage I C.stock hpark)

end PushPuzzle.PushPush.Doors.Source
