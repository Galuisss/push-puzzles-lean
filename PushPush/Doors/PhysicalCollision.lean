/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.PhysicalRegister
public import PushPush.Doors.ForwardInventoryUpdate

/-! Any actual successful two-slot collision has the exact safe control-machine update. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction)

theorem physical_slot_collision {storage : Bool} {I : Instance}
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (ht : Protected storage I t) (door : Fin I.doors.length)
    (moving stationary : Room.Slot) (hne : moving ≠ stationary)
    (hc : Room.Column s (doorCell storage I door 0 (by omega)).1
      (doorBase door.val + (layout storage I).shift) moving stationary)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hb : t.boxes = r.boxes)
    (hfirst : (r.cell ⟨1, by omega⟩).1 = (doorCell storage I door 0 (by omega)).1 ∧
      (r.cell ⟨1, by omega⟩).2.val = doorBase door.val + (layout storage I).shift + moving.row)
    (hd : d = .north ∨ d = .south) :
    n = 1 ∧ r.cell ⟨n + k, by omega⟩ =
      doorCell storage I door (Room.landing moving stationary)
        (by have := landing_bounds moving stationary; omega) := by
  have hfx : (r.cell ⟨1, by omega⟩).1.val = (layout storage I).rackX - 1 :=
    congrArg Fin.val hfirst.1
  have hsafe := ht.slide_door_safe door r hn hb hfx hd
  have hroom : doorBase door.val + (layout storage I).shift + 90 < (layout storage I).height := by
    have hbnd := (layout storage I).translated_bounds
      (dividers_fit storage I (door_south_divider_mem storage I door.isLt))
    omega
  have hcollision := Room.collision r hn hk _ _ moving stationary hne hc hfirst hd hroom hsafe
  refine ⟨hcollision.1, ?_⟩
  apply Prod.ext <;> apply Fin.ext
  · have hfl := r.lane ⟨1, by omega⟩
    have hll := r.lane ⟨n + k, by omega⟩
    change (r.cell ⟨n + k, by omega⟩).1.val = (layout storage I).rackX - 1
    rcases hd with rfl | rfl <;> simp only [Direction.lane] at hfl hll <;> omega
  · change (r.cell ⟨n + k, by omega⟩).2.val =
      doorBase door.val + Room.landing moving stationary + (layout storage I).shift
    omega

theorem ofSlot_injective : Function.Injective Register.ofSlot := by
  intro first second he
  cases first <;> cases second <;> simp_all [Register.ofSlot]

/-- A single-box signal slide realizes any matching finite control path with the same registers. -/
theorem Control.signal_slide {storage : Bool} {I : Instance} {current next : Control storage I}
    (hcontrol : Control.Reachable current next) (hregular : next.signal.Regular)
    (hregister : next.register = current.register)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : current.stock.Realizes storage s) {d : Direction} {k : ℕ}
    (r : Slide d s 1 k) (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) = current.stock.signal)
    (hclear : r.cell ⟨1, by omega⟩ ∉ current.stock.stationary storage)
    (hlast : next.signal.point = ((r.cell ⟨k + 1, by omega⟩).1.val,
      (r.cell ⟨k + 1, by omega⟩).2.val)) : current.PhysicalNext t := by
  have hnext : next.stock = ({current.stock with signal :=
      ((r.cell ⟨k + 1, by omega⟩).1.val, (r.cell ⟨k + 1, by omega⟩).2.val)} : Stock I) :=
    Stock.eq_of_register_signal hregister hlast
  have hboxes := current.stock.boxes_setSignal storage (r.cell ⟨1, by omega⟩)
    (r.cell ⟨k + 1, by omega⟩) hfirst.symm hclear
  rw [← hnext] at hboxes
  refine ⟨next, hcontrol, hregular, ?_⟩
  change t.boxes = next.stock.boxes storage
  rw [hb, single_slide_boxes r, hstock]
  exact hboxes.symm

/-- The two possible single-box interactions in a real input room are exactly the
two collision constructors of the safe control machine. -/
private theorem Control.call_push {storage : Bool} {I : Instance}
    (register : Fin I.doors.length → Register) (door : Fin I.doors.length)
    (stored incoming : Room.Slot) (hregister : register door = Register.ofSlot stored)
    (hdifferent : stored ≠ incoming)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (ht : Protected storage I t)
    (hstock : (⟨register, .working (doorBase door.val + incoming.row)⟩ : Control storage I).stock.Realizes storage s)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hb : t.boxes = r.boxes)
    (hfirst : r.cell ⟨1, by omega⟩ = doorCell storage I door stored.row
        (by have := Room.slot_row_bounds stored; omega) ∨
      r.cell ⟨1, by omega⟩ = doorCell storage I door incoming.row
        (by have := Room.slot_row_bounds incoming; omega))
    (hd : d = .north ∨ d = .south) :
    (⟨register, .working (doorBase door.val + incoming.row)⟩ : Control storage I).PhysicalNext t := by
  let current : Control storage I := ⟨register, .working (doorBase door.val + incoming.row)⟩
  let S := current.stock
  have hsreg : S.register door = Register.ofSlot stored := hregister
  have hsig : S.signal = atRow storage I (doorBase door.val + (Register.ofSlot incoming).row) := by
    simp only [S, current, Control.stock, SignalPosition.point, atRow, Register.row_ofSlot]
  have hnereg : S.register door ≠ Register.ofSlot incoming := by
    rw [hsreg]
    exact fun he => hdifferent (ofSlot_injective he)
  have hnereg' : register door ≠ Register.ofSlot incoming := hnereg
  have hc := S.input_column door stored incoming hsreg
    (by simp only [S, current, Control.stock, SignalPosition.point]) hstock
  have hdata : S.doorPoint storage door =
      doorCell storage I door stored.row (by have := Room.slot_row_bounds stored; omega) := by
    apply Prod.ext <;> apply Fin.ext
    · rfl
    · change doorBase door.val + (S.register door).row + (layout storage I).shift = _
      rw [hsreg, Register.row_ofSlot]
      rfl
  rcases hfirst with hfirst | hfirst
  · have hfirst' : (r.cell ⟨1, by omega⟩).1 = (doorCell storage I door 0 (by omega)).1 ∧
        (r.cell ⟨1, by omega⟩).2.val = doorBase door.val + (layout storage I).shift + stored.row := by
      rw [hfirst]
      exact ⟨rfl, by change doorBase door.val + stored.row + (layout storage I).shift = _; omega⟩
    obtain ⟨rfl, hlast⟩ := physical_slot_collision ht door stored incoming hdifferent hc r hn hk hb hfirst' hd
    have hlast' : r.cell ⟨k + 1, by omega⟩ =
        doorCell storage I door (Room.landing stored incoming) (by have := landing_bounds stored incoming; omega) := by
      have hi : (⟨k + 1, by omega⟩ : Fin (1 + k + 1)) = ⟨1 + k, by omega⟩ :=
        Fin.ext (by change k + 1 = 1 + k; omega)
      rw [hi]
      exact hlast
    let next : Control storage I := ⟨Function.update register door (Register.ofSlot incoming),
      .working (doorBase door.val + Room.landing stored incoming)⟩
    have hstep : Control.Step current next := by
      simpa only [current, next, hregister, Register.row_ofSlot, collisionRow_ofSlot] using
        Control.Step.moveStored (storage := storage) register door (Register.ofSlot incoming) hnereg'
    refine ⟨next, Relation.ReflTransGen.single hstep, trivial, ?_⟩
    have hboxes := S.boxes_after_collision storage door (Register.ofSlot incoming) hnereg hsig
    simp only [hsreg, collisionRow_ofSlot, hdata] at hboxes
    change next.stock.boxes storage = _ at hboxes
    change t.boxes = next.stock.boxes storage
    rw [hb, single_slide_boxes r, hfirst, hlast', hstock]
    exact hboxes.symm
  · have hfirst' : (r.cell ⟨1, by omega⟩).1 = (doorCell storage I door 0 (by omega)).1 ∧
        (r.cell ⟨1, by omega⟩).2.val = doorBase door.val + (layout storage I).shift + incoming.row := by
      rw [hfirst]
      exact ⟨rfl, by change doorBase door.val + incoming.row + (layout storage I).shift = _; omega⟩
    obtain ⟨rfl, hlast⟩ := physical_slot_collision ht door incoming stored hdifferent.symm
      (column_swap hc) r hn hk hb hfirst' hd
    have hlast' : r.cell ⟨k + 1, by omega⟩ =
        doorCell storage I door (Room.landing incoming stored) (by have := landing_bounds incoming stored; omega) := by
      have hi : (⟨k + 1, by omega⟩ : Fin (1 + k + 1)) = ⟨1 + k, by omega⟩ :=
        Fin.ext (by change k + 1 = 1 + k; omega)
      rw [hi]
      exact hlast
    let sourceCell := doorCell storage I door incoming.row (by have := Room.slot_row_bounds incoming; omega)
    let destCell := doorCell storage I door (Room.landing incoming stored) (by have := landing_bounds incoming stored; omega)
    have hclear : sourceCell ∉ S.stationary storage := by
      intro hp
      have hp := ((layout storage I).mem_raster _ _).mp hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact fixed_door_clear storage I door sourceCell rfl
          (by have := Room.slot_row_bounds incoming; dsimp [sourceCell]; omega)
          (by have := Room.slot_row_bounds incoming; dsimp [sourceCell]; omega) hp
      · apply S.door_input_ready storage door (Register.ofSlot incoming) hnereg
        simpa only [atRow, Register.row_ofSlot, sourceCell, doorCell_x, doorCell_y] using hp
    let next : Control storage I := ⟨register, .working (doorBase door.val + Room.landing incoming stored)⟩
    have hstep : Control.Step current next := by
      simpa only [current, next, hregister, Register.row_ofSlot, collisionRow_ofSlot] using
        Control.Step.moveSignal (storage := storage) register door (Register.ofSlot incoming) hnereg'
    refine ⟨next, Relation.ReflTransGen.single hstep, trivial, ?_⟩
    have hboxes := S.boxes_setSignal storage sourceCell destCell
      (by simp only [S, current, Control.stock, SignalPosition.point]; rfl) hclear
    change next.stock.boxes storage = insert destCell ((S.boxes storage).erase sourceCell) at hboxes
    change t.boxes = next.stock.boxes storage
    rw [hb, single_slide_boxes r, hfirst, hlast', hstock]
    exact hboxes.symm

theorem ControlPhase.register_push {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (hphase : ControlPhase storage I source C) (hregular : C.signal.Regular)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) (ht : Protected storage I t) (hstock : C.stock.Realizes storage s)
    (door : Fin I.doors.length) {d : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k) (hv : s.player ∉ s.boxes)
    (hb : t.boxes = r.boxes) (hfirst : r.cell ⟨1, by omega⟩ = C.stock.doorPoint storage door) :
    C.PhysicalNext t := by
  obtain ⟨channel, stored, incoming, _, hsession, rfl, hdv⟩ :=
    hphase.register_call hregular hs ht hstock door r hn hk hv hb hfirst
  have hdistinct := Room.reachable_call_distinct (source.bits.getD door.val false)
    channel stored incoming hsession
  have hdata : r.cell ⟨1, by omega⟩ = doorCell storage I door stored.row
      (by have := Room.slot_row_bounds stored; omega) := by
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg (fun p => p.1.val) hfirst
    · have hy := congrArg (fun p => p.2.val) hfirst
      change (r.cell ⟨1, by omega⟩).2.val = doorBase door.val +
        (sessionRegisters I source door stored door).row + (layout storage I).shift at hy
      rw [sessionRegisters_self, Register.row_ofSlot] at hy
      exact hy
  exact Control.call_push (sessionRegisters I source door stored) door stored incoming
    (sessionRegisters_self I source door stored) hdistinct ht hstock r hn hk hb (Or.inl hdata) hdv

/-- A signal pushed from a genuine input slot performs the other permitted collision choice. -/
theorem ControlPhase.signal_call_push {storage : Bool} {I : Instance} {source : State}
    (door : Fin I.doors.length) (channel : Bool) (stored incoming : Room.Slot)
    (hsession : Room.Reachable
      (.call (Room.stable (source.bits.getD door.val false)) (Room.check channel))
      (.call stored incoming))
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) (ht : Protected storage I t)
    (hstock : (⟨sessionRegisters I source door stored,
      .working (doorBase door.val + incoming.row)⟩ : Control storage I).stock.Realizes storage s)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) =
      ((layout storage I).rackX - 1, doorBase door.val + incoming.row + (layout storage I).shift)) :
    (⟨sessionRegisters I source door stored,
      .working (doorBase door.val + incoming.row)⟩ : Control storage I).PhysicalNext t := by
  have hcell : r.cell ⟨1, by omega⟩ = doorCell storage I door incoming.row
      (by have := Room.slot_row_bounds incoming; omega) := by
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst hfirst
    · exact congrArg Prod.snd hfirst
  have hfull := hs.input_rack_box
    (door_slot_rack_mem storage I (offset := incoming.row) door.isLt
      (by cases incoming <;> simp [Room.Slot.row]))
    (r.cell ⟨1, by omega⟩) (congrArg Prod.fst hfirst) (congrArg Prod.snd hfirst)
  have hdv : d = .north ∨ d = .south := by
    by_contra h
    have hdh : d = .east ∨ d = .west := by cases d <;> simp_all
    exact hs.full_rack_no_horizontal ht r hn hk hv hb hfull hdh
  have hdistinct := Room.reachable_call_distinct (source.bits.getD door.val false)
    channel stored incoming hsession
  exact Control.call_push (sessionRegisters I source door stored) door stored incoming
    (sessionRegisters_self I source door stored) hdistinct ht hstock r hn hk hb (Or.inr hcell) hdv

end PushPuzzle.PushPush.Doors.Source
