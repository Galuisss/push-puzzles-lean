/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.PhysicalState
public import PushPush.Doors.RoomCollision

/-! Resting door boxes cannot move during successful physical prefixes. -/

@[expose] public section
namespace PushPuzzle.PushPush

open PushFS (Cell State Direction Adjacent)

theorem Slide.last_mem_boxes {w h n k : ℕ} {d : Direction} {s : State w h}
    (r : Slide d s n k) (hn : 0 < n) : r.cell ⟨n + k, by omega⟩ ∈ r.boxes := by
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨⟨n - 1, by omega⟩, Finset.mem_univ _, ?_⟩
  congr 1
  apply Fin.ext
  change k + (n - 1) + 1 = n + k
  omega

namespace Doors.Source

private theorem register_ofSlot_of_ne_erase (value : Register) (hne : value ≠ .erase) :
    ∃ slot : Room.Slot, value = Register.ofSlot slot := by
  cases value
  · exact ⟨.low, rfl⟩
  · exact ⟨.a, rfl⟩
  · exact ⟨.checkA, rfl⟩
  · exact ⟨.checkB, rfl⟩
  · exact ⟨.b, rfl⟩
  · exact False.elim (hne rfl)
  · exact ⟨.high, rfl⟩

theorem Protected.door_neighbors_empty {storage : Bool} {I : Instance}
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) (door : Fin I.doors.length)
    (p : Cell (layout storage I).width (layout storage I).height)
    (hx : p.1.val = (layout storage I).rackX - 1)
    (hy : p.2.val = doorBase door.val + (layout storage I).shift + 1 ∨
      p.2.val = doorBase door.val + (layout storage I).shift + 89) : p ∉ s.boxes := by
  rcases hy with hy | hy
  · have hg := hs.dividers (doorBase door.val) (door_divider_mem storage I door.isLt)
      (doorCell storage I door 0 (by omega)) rfl (by simp)
    apply hg.2 p
    apply Or.inr
    exact ⟨Fin.ext hx, by change p.2.val = doorBase door.val + 0 + (layout storage I).shift + 1; omega⟩
  · have hg := hs.dividers (doorBase door.val + 90) (door_south_divider_mem storage I door.isLt)
      (doorCell storage I door 90 (by omega)) rfl (by simp [Nat.add_assoc])
    apply hg.2 p
    apply Or.inl
    exact ⟨Fin.ext hx, by change p.2.val + 1 = doorBase door.val + 90 + (layout storage I).shift; omega⟩

theorem Protected.input_rack_box {storage : Bool} {I : Instance}
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) {row : ℕ} (hrow : row ∈ (layout storage I).rackRows)
    (p : Cell (layout storage I).width (layout storage I).height)
    (hx : p.1.val = (layout storage I).rackX - 1)
    (hy : p.2.val = row + (layout storage I).shift) :
    ∃ e, Adjacent .east p e ∧ e.1.val = (layout storage I).rackX ∧ e ∈ s.boxes := by
  have hr := (layout storage I).rackX_ge
  have hwidth : (layout storage I).rackX < (layout storage I).width := by unfold Layout.width; omega
  let e : Cell (layout storage I).width (layout storage I).height :=
    (⟨(layout storage I).rackX, hwidth⟩, p.2)
  refine ⟨e, ⟨by change (layout storage I).rackX = p.1.val + 1; omega, rfl⟩, rfl, ?_⟩
  apply (rack_mem_iff (show e.1.val = (layout storage I).rackX from rfl) hs.rack).mpr
  apply ((layout storage I).mem_raster _ _).mpr
  change ((layout storage I).rackX, p.2.val) ∈ (layout storage I).initialRaw
  rw [hy, (layout storage I).initialRaw_rack_iff]
  exact ((layout storage I).mem_rack_iff _).mpr (Or.inl ⟨row, hrow, rfl⟩)

theorem Protected.full_rack_no_horizontal {storage : Bool} {I : Instance}
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) (ht : Protected storage I t)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (hb : t.boxes = r.boxes)
    (heast : ∃ e, Adjacent .east (r.cell ⟨1, by omega⟩) e ∧
      e.1.val = (layout storage I).rackX ∧ e ∈ s.boxes)
    (hd : d = .east ∨ d = .west) : False := by
  obtain ⟨e, he, hex, heb⟩ := heast
  have hbefore : r.cell ⟨1, by omega⟩ ∈ r.before :=
    Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩
  have hea : Adjacent d (r.cell ⟨1, by omega⟩) e ∨ Adjacent d e (r.cell ⟨1, by omega⟩) := by
    rcases hd with rfl | rfl
    · exact Or.inl he
    · exact Or.inr he.reverse
  have hebefore := r.before_adjacent hk hv hbefore heb hea
  have hi : ∀ p ∈ r.boxes, ¬ Boundary p := by simpa only [Interior, hb] using ht.interior
  have hrack : line .south (layout storage I).rackX r.boxes =
      line .south (layout storage I).rackX s.boxes := by rw [← hb]; exact ht.rack.trans hs.rack.symm
  exact r.horizontal_before_not_rack hn hk hd hs.supported hi hrack hebefore hex

theorem Protected.slide_door_safe {storage : Bool} {I : Instance}
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (ht : Protected storage I t) (door : Fin I.doors.length)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n)
    (hb : t.boxes = r.boxes)
    (hfirstx : (r.cell ⟨1, by omega⟩).1.val = (layout storage I).rackX - 1)
    (hd : d = .north ∨ d = .south) :
    (r.cell ⟨n + k, by omega⟩).2.val ≠ doorBase door.val + (layout storage I).shift + 1 ∧
      (r.cell ⟨n + k, by omega⟩).2.val ≠ doorBase door.val + (layout storage I).shift + 89 := by
  have hlastx : (r.cell ⟨n + k, by omega⟩).1.val = (layout storage I).rackX - 1 := by
    have hfl := r.lane ⟨1, by omega⟩
    have hll := r.lane ⟨n + k, by omega⟩
    rcases hd with rfl | rfl <;> simp only [Direction.lane] at hfl hll <;> omega
  constructor <;> intro hy
  · exact ht.door_neighbors_empty door _ hlastx (Or.inl hy) (hb ▸ r.last_mem_boxes hn)
  · exact ht.door_neighbors_empty door _ hlastx (Or.inr hy) (hb ▸ r.last_mem_boxes hn)

namespace Stock

variable {storage : Bool} {I : Instance}

/-- The active signal is outside the selected complete door column. -/
def SignalOutsideDoor (S : Stock I) (storage : Bool) (door : Fin I.doors.length) : Prop :=
  ∀ p : Cell (layout storage I).width (layout storage I).height,
    p.1.val = (layout storage I).rackX - 1 →
    doorBase door.val + (layout storage I).shift ≤ p.2.val →
    p.2.val ≤ doorBase door.val + (layout storage I).shift + 90 →
      (p.1.val, p.2.val) ≠ S.signal

theorem solo_column (S : Stock I) (door : Fin I.doors.length)
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : S.Realizes storage s) (houtside : S.SignalOutsideDoor storage door) :
    Room.SoloColumn s (S.doorPoint storage door).1
      (doorBase door.val + (layout storage I).shift) (S.register door).row := by
  intro p hx hlo hhi
  have hpx : p.1.val = (layout storage I).rackX - 1 := congrArg Fin.val hx
  have hc := S.door_column storage door hs p hpx hlo hhi
  have hout := houtside p hpx hlo hhi
  constructor
  · intro hp
    rcases hc.mp hp with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by omega))
    · exact False.elim (hout h)
  · rintro (h | h | h)
    · exact hc.mpr (Or.inl h)
    · exact hc.mpr (Or.inr (Or.inl h))
    · exact hc.mpr (Or.inr (Or.inr (Or.inl (by omega))))

theorem register_no_horizontal (S : Stock I) (door : Fin I.doors.length)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) (ht : Protected storage I t)
    (hreg : S.register door ≠ .erase) {d : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k) (hv : s.player ∉ s.boxes)
    (hb : t.boxes = r.boxes) (hfirst : r.cell ⟨1, by omega⟩ = S.doorPoint storage door)
    (hd : d = .east ∨ d = .west) : False := by
  obtain ⟨slot, hslot⟩ := register_ofSlot_of_ne_erase (S.register door) hreg
  let first := S.doorPoint storage door
  have hwidth : (layout storage I).rackX < (layout storage I).width := by
    unfold Layout.width
    omega
  let east : Cell (layout storage I).width (layout storage I).height :=
    (⟨(layout storage I).rackX, hwidth⟩, first.2)
  have he : Adjacent .east first east := by
    constructor
    · change (layout storage I).rackX = (layout storage I).rackX - 1 + 1
      have := (layout storage I).rackX_ge
      omega
    · rfl
  have heinitial : east ∈ (puzzle storage I).initial.boxes := by
    apply ((layout storage I).mem_raster _ _).mpr
    change ((layout storage I).rackX, doorBase door.val + (S.register door).row +
      (layout storage I).shift) ∈ (layout storage I).initialRaw
    rw [(layout storage I).initialRaw_rack_iff]
    apply ((layout storage I).mem_rack_iff _).mpr
    refine Or.inl ⟨doorBase door.val + slot.row, ?_, ?_⟩
    · exact door_slot_rack_mem storage I door.isLt (by cases slot <;> simp [Room.Slot.row])
    · rw [hslot, Register.row_ofSlot]
  have hebox : east ∈ s.boxes := (rack_mem_iff rfl hs.rack).mpr heinitial
  have hfirstbefore : first ∈ r.before := by
    change S.doorPoint storage door ∈ r.before
    rw [← hfirst]
    exact Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩
  have hae : Adjacent d first east ∨ Adjacent d east first := by
    rcases hd with rfl | rfl
    · exact Or.inl he
    · exact Or.inr he.reverse
  have hebefore := r.before_adjacent hk hv hfirstbefore hebox hae
  have hi : ∀ p ∈ r.boxes, ¬ Boundary p := by simpa only [Interior, hb] using ht.interior
  have hrack : line .south (layout storage I).rackX r.boxes =
      line .south (layout storage I).rackX s.boxes := by rw [← hb]; exact ht.rack.trans hs.rack.symm
  exact r.horizontal_before_not_rack hn hk hd hs.supported hi hrack hebefore rfl

theorem idle_register_no_vertical (S : Stock I) (door : Fin I.doors.length)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : S.Realizes storage s) (ht : Protected storage I t)
    (houtside : S.SignalOutsideDoor storage door) {d : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k) (hb : t.boxes = r.boxes)
    (hfirst : r.cell ⟨1, by omega⟩ = S.doorPoint storage door)
    (hd : d = .north ∨ d = .south) : False := by
  have hrow := Register.row_bounds (S.register door)
  have hroom : doorBase door.val + (layout storage I).shift + 90 < (layout storage I).height := by
    have hbnd := (layout storage I).translated_bounds
      (dividers_fit storage I (door_south_divider_mem storage I door.isLt))
    omega
  have hc := Room.solo_collision r hn hk (S.doorPoint storage door).1
    (doorBase door.val + (layout storage I).shift) (S.register door).row hroom
    (by omega) (S.solo_column door hstock houtside)
    ⟨congrArg Prod.fst hfirst, by
      rw [hfirst]
      change doorBase door.val + (S.register door).row + (layout storage I).shift =
        doorBase door.val + (layout storage I).shift + (S.register door).row
      omega⟩ hd
  have hlast := r.last_mem_boxes hn
  have hlx : (r.cell ⟨n + k, by omega⟩).1.val = (layout storage I).rackX - 1 := by
    have hfl := r.lane ⟨1, by omega⟩
    have hll := r.lane ⟨n + k, by omega⟩
    rw [hfirst] at hfl
    rcases hd with rfl | rfl <;> simp only [Direction.lane] at hfl hll <;>
      change (layout storage I).rackX - 1 = s.player.1.val at hfl <;> omega
  exact ht.door_neighbors_empty door _ hlx hc.2 (hb ▸ hlast)

end Stock
end Doors.Source
end PushPuzzle.PushPush
