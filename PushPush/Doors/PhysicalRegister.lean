/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.PhysicalPair

/-! A register can move only in the unique active two-slot door call. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction)

theorem ControlPhase.register_active {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C) (hregular : C.signal.Regular)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) (ht : Protected storage I t) (hstock : C.stock.Realizes storage s)
    (door : Fin I.doors.length) {d : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k) (hv : s.player ∉ s.boxes)
    (hb : t.boxes = r.boxes) (hfirst : r.cell ⟨1, by omega⟩ = C.stock.doorPoint storage door) :
    ActiveDoor storage I source door C ∧ (d = .north ∨ d = .south) := by
  have hdv : d = .north ∨ d = .south := by
    by_contra h
    have hdh : d = .east ∨ d = .west := by cases d <;> simp_all
    exact C.stock.register_no_horizontal door hs ht (hphase.register_ne_erase door)
      r hn hk hv hb hfirst hdh
  rcases hphase.outside_or_active hregular door with hout | hactive
  · exact False.elim (C.stock.idle_register_no_vertical door hstock ht hout r hn hk hb hfirst hdv)
  · exact ⟨hactive, hdv⟩

private theorem Stock.pair_register_no_vertical {storage : Bool} {I : Instance}
    (S : Stock I) (door : Fin I.doors.length) (moving kept : Room.Slot)
    (hregister : S.register door = Register.ofSlot kept)
    (hsignal : S.signal = ((layout storage I).rackX - 1,
      doorBase door.val + Room.landing moving kept + (layout storage I).shift))
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : S.Realizes storage s) (ht : Protected storage I t)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (hb : t.boxes = r.boxes)
    (hfirst : r.cell ⟨1, by omega⟩ = S.doorPoint storage door)
    (hdv : d = .north ∨ d = .south) : False := by
  have hpair := S.pair_column door moving kept hregister hsignal hstock
  have hbounds := pairLower_bounds (doorBase door.val + (layout storage I).shift) moving kept
  have hfirstx : (r.cell ⟨1, by omega⟩).1 = (doorCell storage I door 0 (by omega)).1 := by
    rw [hfirst]
    rfl
  have hfirsty : (r.cell ⟨1, by omega⟩).2.val =
      doorBase door.val + (layout storage I).shift + kept.row := by
    rw [hfirst]
    change doorBase door.val + (S.register door).row + (layout storage I).shift = _
    rw [hregister, Register.row_ofSlot]
    omega
  have hy := (pairLower_inventory (doorBase door.val + (layout storage I).shift)
    (r.cell ⟨1, by omega⟩).2.val moving kept).mp (Or.inl hfirsty)
  exact ht.pair_door_no_vertical door _ hbounds.1 hbounds.2 hpair r hn hk hv hb hfirstx hy hdv

/-- Every physically moved register identifies the same original active call and its two slots. -/
theorem ControlPhase.register_call {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C) (hregular : C.signal.Regular)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) (ht : Protected storage I t) (hstock : C.stock.Realizes storage s)
    (door : Fin I.doors.length) {d : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k) (hv : s.player ∉ s.boxes)
    (hb : t.boxes = r.boxes) (hfirst : r.cell ⟨1, by omega⟩ = C.stock.doorPoint storage door) :
    ∃ channel stored incoming,
      source.location = (I.doors[door].tunnel channel).source ∧
      Room.Reachable (.call (Room.stable (source.bits.getD door.val false)) (Room.check channel))
        (.call stored incoming) ∧
      C = ⟨sessionRegisters I source door stored, .working (doorBase door.val + incoming.row)⟩ ∧
      (d = .north ∨ d = .south) := by
  obtain ⟨hactive, hdv⟩ := hphase.register_active hregular hs ht hstock door r hn hk hv hb hfirst
  cases hactive with
  | call channel stored incoming hentry hsession =>
    exact ⟨channel, stored, incoming, hentry, hsession, rfl, hdv⟩
  | result channel stored incoming keep hentry hsession =>
    apply False.elim
    cases keep
    · exact Stock.pair_register_no_vertical _ door incoming stored (by simp [Control.stock])
        rfl hstock ht r hn hk hv hb hfirst hdv
    · exact Stock.pair_register_no_vertical _ door stored incoming (by simp [Control.stock])
        rfl hstock ht r hn hk hv hb hfirst hdv

end PushPuzzle.PushPush.Doors.Source
