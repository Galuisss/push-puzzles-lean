/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.PhysicalPhase

/-! Actual two-slot and adjacent-pair chamber inventories from complete physical stocks. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell)

theorem column_swap {w h : ℕ} {s : PushFS.State w h} {x : Fin w} {g : ℕ}
    {moving stationary : Room.Slot} (hc : Room.Column s x g moving stationary) :
    Room.Column s x g stationary moving := by
  intro p hx hlo hhi
  have hh := hc p hx hlo hhi
  tauto

/-- Lower row of the adjacent pair created by one room collision. -/
def pairLower (g : ℕ) (moving kept : Room.Slot) : ℕ :=
  g + min kept.row (Room.landing moving kept)

theorem pairLower_bounds (g : ℕ) (moving kept : Room.Slot) :
    g + 3 ≤ pairLower g moving kept ∧ pairLower g moving kept + 3 ≤ g + 90 := by
  have hs := Room.slot_row_bounds kept
  have hl := landing_bounds moving kept
  unfold pairLower
  omega

theorem pairLower_inventory (g z : ℕ) (moving kept : Room.Slot) :
    (z = g + kept.row ∨ z = g + Room.landing moving kept) ↔
      z = pairLower g moving kept ∨ z = pairLower g moving kept + 1 := by
  have ha := Room.landing_adjacent moving kept
  unfold pairLower
  omega

namespace Stock

variable {storage : Bool} {I : Instance}

private theorem signal_eq_row (S : Stock I) (row : ℕ)
    (hsignal : S.signal = ((layout storage I).rackX - 1, row))
    (p : Cell (layout storage I).width (layout storage I).height)
    (hpx : p.1.val = (layout storage I).rackX - 1) :
    (p.1.val, p.2.val) = S.signal ↔ p.2.val = row := by
  rw [hsignal]
  simp only [Prod.mk.injEq, hpx, true_and]

theorem input_column (S : Stock I) (door : Fin I.doors.length) (stored incoming : Room.Slot)
    (hregister : S.register door = Register.ofSlot stored)
    (hsignal : S.signal = ((layout storage I).rackX - 1,
      doorBase door.val + incoming.row + (layout storage I).shift))
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : S.Realizes storage s) :
    Room.Column s (doorCell storage I door 0 (by omega)).1
      (doorBase door.val + (layout storage I).shift) stored incoming := by
  intro p hx hlo hhi
  have hpx : p.1.val = (layout storage I).rackX - 1 := congrArg Fin.val hx
  have hc := S.door_column storage door hs p hpx hlo hhi
  rw [hregister, Register.row_ofSlot, signal_eq_row S _ hsignal p hpx] at hc
  have hstored : doorBase door.val + stored.row + (layout storage I).shift =
      doorBase door.val + (layout storage I).shift + stored.row := by omega
  have hincoming : doorBase door.val + incoming.row + (layout storage I).shift =
      doorBase door.val + (layout storage I).shift + incoming.row := by omega
  rwa [hstored, hincoming] at hc

theorem pair_column (S : Stock I) (door : Fin I.doors.length) (moving kept : Room.Slot)
    (hregister : S.register door = Register.ofSlot kept)
    (hsignal : S.signal = ((layout storage I).rackX - 1,
      doorBase door.val + Room.landing moving kept + (layout storage I).shift))
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : S.Realizes storage s) :
    Room.PairColumn s (doorCell storage I door 0 (by omega)).1
      (doorBase door.val + (layout storage I).shift)
      (pairLower (doorBase door.val + (layout storage I).shift) moving kept) := by
  intro p hx hlo hhi
  have hpx : p.1.val = (layout storage I).rackX - 1 := congrArg Fin.val hx
  have hc := S.door_column storage door hs p hpx hlo hhi
  rw [hregister, Register.row_ofSlot, signal_eq_row S _ hsignal p hpx] at hc
  have hstored : doorBase door.val + kept.row + (layout storage I).shift =
      doorBase door.val + (layout storage I).shift + kept.row := by omega
  have hsignalrow : doorBase door.val + Room.landing moving kept + (layout storage I).shift =
      doorBase door.val + (layout storage I).shift + Room.landing moving kept := by omega
  rw [hstored, hsignalrow, pairLower_inventory] at hc
  exact hc

end Stock
end PushPuzzle.PushPush.Doors.Source
