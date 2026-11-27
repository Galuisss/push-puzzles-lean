/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.PhysicalChamber

/-! Only the door hosting the active working signal can have a nonresting register. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

namespace Stock

variable {storage : Bool} {I : Instance}

private theorem signalOutsideDoor_of_private (S : Stock I) (door : Fin I.doors.length)
    (hx : S.signal.1 ≠ (layout storage I).rackX - 1) : S.SignalOutsideDoor storage door := by
  intro p hpx _ _ he
  exact hx ((congrArg Prod.fst he).symm.trans hpx)

private theorem signalOutsideDoor_of_junction (S : Stock I) (door : Fin I.doors.length)
    (hy : 90 * I.doors.length + (layout storage I).shift < S.signal.2) :
    S.SignalOutsideDoor storage door := by
  intro p _ _ hhi he
  have hpy := congrArg Prod.snd he
  have hd := door.isLt
  unfold doorBase at hhi
  omega

private theorem signalOutsideDoor_of_other_door (S : Stock I) (active door : Fin I.doors.length)
    (hne : active ≠ door) {offset : ℕ} (hlo : 0 < offset) (hhi : offset < 90)
    (hy : S.signal.2 = doorBase active.val + offset + (layout storage I).shift) :
    S.SignalOutsideDoor storage door := by
  intro p _ hpl hph he
  have hpy := congrArg Prod.snd he
  have hid : active = door := by
    apply Fin.ext
    unfold doorBase at hy hpl hph
    omega
  exact hne hid

end Stock

/-- The two physical phases in which this original door contains the active signal. -/
inductive ActiveDoor (storage : Bool) (I : Instance) (source : State)
    (door : Fin I.doors.length) : Control storage I → Prop
  | call (channel : Bool) (stored incoming : Room.Slot)
      (entry : source.location = (I.doors[door].tunnel channel).source)
      (session : Room.Reachable
        (.call (Room.stable (source.bits.getD door.val false)) (Room.check channel))
        (.call stored incoming)) :
      ActiveDoor storage I source door
        ⟨sessionRegisters I source door stored, .working (doorBase door.val + incoming.row)⟩
  | result (channel : Bool) (stored incoming : Room.Slot) (keep : Bool)
      (entry : source.location = (I.doors[door].tunnel channel).source)
      (session : Room.Reachable
        (.call (Room.stable (source.bits.getD door.val false)) (Room.check channel))
        (.call stored incoming)) :
      ActiveDoor storage I source door
        ⟨sessionRegisters I source door (if keep then incoming else stored),
          .working (doorBase door.val + if keep then Room.landing stored incoming
            else Room.landing incoming stored)⟩

theorem ControlPhase.outside_or_active {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C)
    (hregular : C.signal.Regular) (door : Fin I.doors.length) :
    C.stock.SignalOutsideDoor storage door ∨ ActiveDoor storage I source door C := by
  cases hphase with
  | junction j p hj hp =>
    apply Or.inl
    apply Stock.signalOutsideDoor_of_junction
    change 90 * I.doors.length + (layout storage I).shift <
      inputRow I (rank I source.location) j p + (layout storage I).shift
    unfold inputRow roomBase
    omega
  | upper j hj hused =>
    apply Or.inl
    apply Stock.signalOutsideDoor_of_junction
    change 90 * I.doors.length + (layout storage I).shift <
      upperRow I (rank I source.location) j + (layout storage I).shift
    unfold upperRow roomBase
    omega
  | lower j hj hused =>
    apply Or.inl
    apply Stock.signalOutsideDoor_of_junction
    change 90 * I.doors.length + (layout storage I).shift <
      lowerRow I (rank I source.location) j + (layout storage I).shift
    have hh := chamberHeight_ge I
    unfold lowerRow roomBase
    omega
  | junctionWire index corner j p hj hp htarget =>
    apply Or.inl
    apply Stock.signalOutsideDoor_of_private
    intro he
    have hpriv := Layout.wirePath_private_x (layout storage I) index (layout storage I).wires[index]
      corner (by intro he0; subst corner; exact Nat.lt_irrefl _ hregular.1)
      (by intro he7; subst corner; exact Nat.lt_irrefl _ hregular.2)
    change (SignalPosition.wire index corner).point.1 = (layout storage I).rackX - 1 at he
    change (SignalPosition.wire index corner).point.1 + 2 < (layout storage I).rackX at hpriv
    omega
  | call active channel stored incoming hentry hsession =>
    by_cases hid : active = door
    · subst active
      exact Or.inr (.call channel stored incoming hentry hsession)
    · apply Or.inl
      have hrow := Room.slot_row_bounds incoming
      exact Stock.signalOutsideDoor_of_other_door _ active door hid (by omega) (by omega) rfl
  | result active channel stored incoming keep hentry hsession =>
    by_cases hid : active = door
    · subst active
      exact Or.inr (.result channel stored incoming keep hentry hsession)
    · apply Or.inl
      cases keep
      · have hrow := landing_bounds incoming stored
        exact Stock.signalOutsideDoor_of_other_door _ active door hid
          (offset := Room.landing incoming stored) (by omega) (by omega)
          (by simp [Control.stock, SignalPosition.point])
      · have hrow := landing_bounds stored incoming
        exact Stock.signalOutsideDoor_of_other_door _ active door hid
          (offset := Room.landing stored incoming) (by omega) (by omega)
          (by simp [Control.stock, SignalPosition.point])
  | doorWire active channel stored incoming index corner hentry hsession htarget =>
    apply Or.inl
    apply Stock.signalOutsideDoor_of_private
    intro he
    have hpriv := Layout.wirePath_private_x (layout storage I) index (layout storage I).wires[index]
      corner (by intro he0; subst corner; exact Nat.lt_irrefl _ hregular.1)
      (by intro he7; subst corner; exact Nat.lt_irrefl _ hregular.2)
    change (SignalPosition.wire index corner).point.1 = (layout storage I).rackX - 1 at he
    change (SignalPosition.wire index corner).point.1 + 2 < (layout storage I).rackX at hpriv
    omega

end PushPuzzle.PushPush.Doors.Source
