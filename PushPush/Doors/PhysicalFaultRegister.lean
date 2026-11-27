/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutFault
public import PushPush.Doors.PhysicalRegister
public import PushPush.Doors.ForwardControl
public import PushPush.Doors.ControlRowParity

/-! Private pin faults leave every resting or collision-pair door register immobile. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction)

theorem WireFault.register_no_slide_working_odd {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C) (hregular : C.signal.Regular)
    (F : WireFault storage I C.stock)
    (hland : ∀ p ∈ F.added, p.1.val < (layout storage I).rackX - 1)
    (row : ℕ) (hodd : row % 2 = 1) (hsignal : C.stock.signal = atRow storage I row)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hboxes : s.boxes = F.boxes) (hs : Protected storage I s) (ht : Protected storage I t)
    (door : Fin I.doors.length) {d : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k) (hv : s.player ∉ s.boxes)
    (hb : t.boxes = r.boxes) (hfirst : r.cell ⟨1, by omega⟩ = C.stock.doorPoint storage door) : False := by
  by_cases hdh : d = .east ∨ d = .west
  · exact C.stock.register_no_horizontal door hs ht (hphase.register_ne_erase door) r hn hk hv hb hfirst hdh
  · have hdv : d = .north ∨ d = .south := by cases d <;> simp_all
    rcases hphase.outside_or_active hregular door with hout | hactive
    · have hcOld := C.stock.solo_column (storage := storage) door
        (s := C.stock.canonical storage) rfl hout
      have hc : Room.SoloColumn s (C.stock.doorPoint storage door).1
          (doorBase door.val + (layout storage I).shift) (C.register door).row := by
        intro p hx hlo hhi
        rw [hboxes, F.working_membership hland p (congrArg Fin.val hx)]
        exact hcOld p hx hlo hhi
      have hrow := Register.row_bounds (C.stock.register door)
      have hrow' := Register.row_bounds (C.register door)
      have hroweq : (C.stock.register door).row = (C.register door).row := rfl
      have hroom : doorBase door.val + (layout storage I).shift + 90 < (layout storage I).height := by
        have hbnd := (layout storage I).translated_bounds
          (dividers_fit storage I (door_south_divider_mem storage I door.isLt))
        omega
      have hcol := Room.solo_collision r hn hk _ _ _ hroom (by omega) hc
        (by
          rw [hfirst]
          exact ⟨rfl, by dsimp [Stock.doorPoint]; omega⟩) hdv
      have hlastx : (r.cell ⟨n + k, by omega⟩).1.val = (layout storage I).rackX - 1 := by
        have hf := r.lane ⟨1, by omega⟩
        have hl := r.lane ⟨n + k, by omega⟩
        rw [hfirst] at hf
        rcases hdv with rfl | rfl <;> simp only [Direction.lane] at hf hl <;>
          dsimp [Stock.doorPoint] at hf <;> omega
      exact ht.door_neighbors_empty door _ hlastx hcol.2 (hb ▸ r.last_mem_boxes hn)
    · cases hactive with
      | call channel stored incoming hentry hsession =>
        have hy := congrArg Prod.snd hsignal
        change doorBase door.val + incoming.row + (layout storage I).shift =
          row + (layout storage I).shift at hy
        have heven := registerRow_even I door (Register.ofSlot incoming)
        rw [Register.row_ofSlot] at heven
        omega
      | result channel stored incoming keep hentry hsession =>
        cases keep
        · have hcOld := Stock.pair_column
            (⟨sessionRegisters I source door stored,
              .working (doorBase door.val + Room.landing incoming stored)⟩ : Control storage I).stock
            door incoming stored (by simp [Control.stock]) rfl
            (s := (⟨sessionRegisters I source door stored,
              .working (doorBase door.val + Room.landing incoming stored)⟩ : Control storage I).stock.canonical storage) rfl
          have hc : Room.PairColumn s (doorCell storage I door 0 (by omega)).1
              (doorBase door.val + (layout storage I).shift)
              (pairLower (doorBase door.val + (layout storage I).shift) incoming stored) := by
            intro p hx hlo hhi
            rw [hboxes, F.working_membership hland p (congrArg Fin.val hx)]
            exact hcOld p hx hlo hhi
          have hy : (r.cell ⟨1, by omega⟩).2.val =
              doorBase door.val + (layout storage I).shift + stored.row := by
            rw [hfirst]
            change doorBase door.val +
              (sessionRegisters I source door stored door).row + (layout storage I).shift = _
            rw [sessionRegisters_self, Register.row_ofSlot]
            omega
          have hfirstx : (r.cell ⟨1, by omega⟩).1 = (doorCell storage I door 0 (by omega)).1 := by
            rw [hfirst]; rfl
          have hpairy := (pairLower_inventory (doorBase door.val + (layout storage I).shift)
            (r.cell ⟨1, by omega⟩).2.val incoming stored).mp (Or.inl hy)
          have hbound := pairLower_bounds (doorBase door.val + (layout storage I).shift) incoming stored
          exact ht.pair_door_no_vertical door _ hbound.1 hbound.2 hc r hn hk hv hb hfirstx hpairy hdv

        · have hcOld := Stock.pair_column
            (⟨sessionRegisters I source door incoming,
              .working (doorBase door.val + Room.landing stored incoming)⟩ : Control storage I).stock
            door stored incoming (by simp [Control.stock]) rfl
            (s := (⟨sessionRegisters I source door incoming,
              .working (doorBase door.val + Room.landing stored incoming)⟩ : Control storage I).stock.canonical storage) rfl
          have hc : Room.PairColumn s (doorCell storage I door 0 (by omega)).1
              (doorBase door.val + (layout storage I).shift)
              (pairLower (doorBase door.val + (layout storage I).shift) stored incoming) := by
            intro p hx hlo hhi
            rw [hboxes, F.working_membership hland p (congrArg Fin.val hx)]
            exact hcOld p hx hlo hhi
          have hy : (r.cell ⟨1, by omega⟩).2.val =
              doorBase door.val + (layout storage I).shift + incoming.row := by
            rw [hfirst]
            change doorBase door.val +
              (sessionRegisters I source door incoming door).row + (layout storage I).shift = _
            rw [sessionRegisters_self, Register.row_ofSlot]
            omega
          have hfirstx : (r.cell ⟨1, by omega⟩).1 = (doorCell storage I door 0 (by omega)).1 := by
            rw [hfirst]; rfl
          have hpairy := (pairLower_inventory (doorBase door.val + (layout storage I).shift)
            (r.cell ⟨1, by omega⟩).2.val stored incoming).mp (Or.inl hy)
          have hbound := pairLower_bounds (doorBase door.val + (layout storage I).shift) stored incoming
          exact ht.pair_door_no_vertical door _ hbound.1 hbound.2 hc r hn hk hv hb hfirstx hpairy hdv

end PushPuzzle.PushPush.Doors.Source
