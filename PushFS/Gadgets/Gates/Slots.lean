/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Basic

/-!
# Complete physical slots of the AND/OR gate tiles

The slot list includes every trigger, auxiliary box, protected turn, buffer and
flip. A signal assignment selects exactly one position per physical identity.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Gates


-- The explicit slot lists must reduce inside dependent Fin indices and finite certificates.
set_option maxRecDepth 65536

/-- The two canonical positions of one fixed physical box. -/
structure Slot where
  /-- The logical port whose phase moves this box. -/
  port : Fin 3
  /-- Position when that port flag is false. -/
  zero : C
  /-- Position when that port flag is true. -/
  one : C
  deriving DecidableEq

def Slot.position (s : Slot) (b : Signals) : C :=
  if b.get s.port then s.one else s.zero

def andCoreSlots : List Slot :=
  [⟨0, (41, 90), (40, 90)⟩,
   ⟨0, (43, 90), (42, 90)⟩,
   ⟨1, (43, 89), (43, 88)⟩,
   ⟨1, (43, 87), (43, 86)⟩,
   ⟨2, (47, 90), (46, 90)⟩,
   ⟨2, (49, 90), (48, 90)⟩,
   ⟨1, (43, 85), (43, 84)⟩,
   ⟨2, (51, 90), (50, 90)⟩,
   ⟨0, (39, 89), (39, 88)⟩,
   ⟨0, (39, 87), (39, 86)⟩]

def andOuterSlots : List Slot :=
  [⟨0, (39, 85), (39, 84)⟩,
   ⟨0, (39, 83), (39, 82)⟩,
   ⟨0, (39, 81), (39, 80)⟩,
   ⟨0, (39, 79), (39, 78)⟩,
   ⟨0, (39, 77), (39, 76)⟩,
   ⟨0, (39, 75), (39, 74)⟩,
   ⟨0, (39, 73), (39, 72)⟩,
   ⟨0, (39, 71), (39, 70)⟩,
   ⟨0, (39, 69), (39, 66)⟩,
   ⟨0, (39, 65), (39, 64)⟩,
   ⟨0, (39, 63), (39, 62)⟩,
   ⟨0, (39, 61), (39, 60)⟩,
   ⟨0, (39, 59), (39, 58)⟩,
   ⟨0, (39, 57), (39, 56)⟩,
   ⟨0, (39, 55), (39, 54)⟩,
   ⟨0, (39, 53), (39, 52)⟩,
   ⟨0, (39, 51), (39, 50)⟩,
   ⟨0, (39, 49), (39, 48)⟩,
   ⟨0, (39, 47), (39, 46)⟩,
   ⟨0, (39, 45), (39, 44)⟩,
   ⟨0, (39, 43), (39, 42)⟩,
   ⟨0, (39, 41), (39, 40)⟩,
   ⟨0, (39, 39), (39, 38)⟩,
   ⟨0, (39, 37), (39, 36)⟩,
   ⟨0, (39, 35), (39, 34)⟩,
   ⟨0, (39, 33), (39, 32)⟩,
   ⟨0, (39, 31), (39, 30)⟩,
   ⟨0, (38, 29), (37, 29)⟩,
   ⟨0, (36, 29), (35, 29)⟩,
   ⟨0, (34, 29), (33, 29)⟩,
   ⟨0, (32, 29), (31, 29)⟩,
   ⟨0, (30, 29), (29, 29)⟩,
   ⟨0, (28, 29), (27, 29)⟩,
   ⟨0, (26, 29), (25, 29)⟩,
   ⟨0, (24, 29), (23, 29)⟩,
   ⟨0, (22, 29), (19, 29)⟩,
   ⟨0, (18, 29), (17, 29)⟩,
   ⟨0, (16, 29), (15, 29)⟩,
   ⟨0, (14, 29), (13, 29)⟩,
   ⟨0, (12, 29), (11, 29)⟩,
   ⟨0, (10, 29), (9, 29)⟩,
   ⟨0, (8, 29), (7, 29)⟩,
   ⟨0, (6, 29), (5, 29)⟩,
   ⟨0, (4, 29), (3, 29)⟩,
   ⟨0, (2, 29), (1, 29)⟩,
   ⟨1, (43, 83), (43, 82)⟩,
   ⟨1, (43, 81), (43, 80)⟩,
   ⟨1, (43, 79), (43, 78)⟩,
   ⟨1, (43, 77), (43, 76)⟩,
   ⟨1, (43, 75), (43, 74)⟩,
   ⟨1, (43, 73), (43, 72)⟩,
   ⟨1, (43, 71), (43, 70)⟩,
   ⟨1, (43, 69), (43, 68)⟩,
   ⟨1, (43, 67), (43, 66)⟩,
   ⟨1, (43, 65), (43, 64)⟩,
   ⟨1, (43, 63), (43, 62)⟩,
   ⟨1, (43, 61), (43, 60)⟩,
   ⟨1, (43, 59), (43, 58)⟩,
   ⟨1, (43, 57), (43, 56)⟩,
   ⟨1, (43, 55), (43, 54)⟩,
   ⟨1, (43, 53), (43, 52)⟩,
   ⟨1, (43, 51), (43, 50)⟩,
   ⟨1, (43, 49), (43, 48)⟩,
   ⟨1, (43, 47), (43, 46)⟩,
   ⟨1, (43, 45), (43, 44)⟩,
   ⟨1, (43, 43), (43, 42)⟩,
   ⟨1, (43, 41), (43, 40)⟩,
   ⟨1, (43, 39), (43, 38)⟩,
   ⟨1, (43, 37), (43, 36)⟩,
   ⟨1, (43, 35), (43, 34)⟩,
   ⟨1, (43, 33), (43, 32)⟩,
   ⟨1, (43, 31), (43, 30)⟩,
   ⟨1, (43, 29), (43, 28)⟩,
   ⟨1, (43, 27), (43, 26)⟩,
   ⟨1, (43, 25), (43, 24)⟩,
   ⟨1, (43, 23), (43, 22)⟩,
   ⟨1, (43, 21), (43, 20)⟩,
   ⟨1, (43, 19), (43, 16)⟩,
   ⟨1, (43, 15), (43, 14)⟩,
   ⟨1, (43, 13), (43, 12)⟩,
   ⟨1, (43, 11), (43, 10)⟩,
   ⟨1, (43, 9), (43, 8)⟩,
   ⟨1, (43, 7), (43, 6)⟩,
   ⟨1, (43, 5), (43, 4)⟩,
   ⟨1, (43, 3), (43, 2)⟩,
   ⟨2, (53, 90), (52, 90)⟩,
   ⟨2, (55, 90), (54, 90)⟩,
   ⟨2, (57, 90), (56, 90)⟩,
   ⟨2, (59, 90), (58, 90)⟩,
   ⟨2, (63, 90), (60, 90)⟩,
   ⟨2, (65, 90), (64, 90)⟩,
   ⟨2, (67, 90), (66, 90)⟩,
   ⟨2, (69, 90), (68, 90)⟩,
   ⟨2, (71, 90), (70, 90)⟩,
   ⟨2, (73, 90), (72, 90)⟩,
   ⟨2, (75, 90), (74, 90)⟩,
   ⟨2, (77, 90), (76, 90)⟩,
   ⟨2, (79, 90), (78, 90)⟩]

def orCoreSlots : List Slot :=
  [⟨0, (41, 90), (40, 90)⟩,
   ⟨0, (43, 90), (42, 90)⟩,
   ⟨1, (44, 89), (44, 88)⟩,
   ⟨1, (44, 87), (44, 86)⟩,
   ⟨2, (48, 90), (47, 90)⟩,
   ⟨2, (50, 90), (49, 90)⟩,
   ⟨1, (44, 85), (44, 84)⟩,
   ⟨2, (52, 90), (51, 90)⟩,
   ⟨0, (39, 90), (38, 90)⟩]

def orOuterSlots : List Slot :=
  [⟨0, (37, 90), (36, 90)⟩,
   ⟨0, (35, 90), (34, 90)⟩,
   ⟨0, (33, 90), (32, 90)⟩,
   ⟨0, (31, 90), (30, 90)⟩,
   ⟨0, (29, 90), (28, 90)⟩,
   ⟨0, (27, 90), (26, 90)⟩,
   ⟨0, (25, 90), (24, 90)⟩,
   ⟨0, (23, 90), (20, 90)⟩,
   ⟨0, (19, 90), (18, 90)⟩,
   ⟨0, (17, 90), (16, 90)⟩,
   ⟨0, (15, 90), (14, 90)⟩,
   ⟨0, (13, 90), (12, 90)⟩,
   ⟨0, (11, 90), (10, 90)⟩,
   ⟨0, (9, 90), (8, 90)⟩,
   ⟨0, (7, 90), (6, 90)⟩,
   ⟨0, (5, 90), (4, 90)⟩,
   ⟨0, (3, 90), (2, 90)⟩,
   ⟨1, (44, 83), (44, 82)⟩,
   ⟨1, (44, 81), (44, 80)⟩,
   ⟨1, (44, 79), (44, 78)⟩,
   ⟨1, (44, 77), (44, 76)⟩,
   ⟨1, (44, 75), (44, 74)⟩,
   ⟨1, (44, 73), (44, 72)⟩,
   ⟨1, (44, 71), (44, 70)⟩,
   ⟨1, (44, 69), (44, 68)⟩,
   ⟨1, (44, 67), (44, 66)⟩,
   ⟨1, (44, 65), (44, 64)⟩,
   ⟨1, (44, 63), (44, 62)⟩,
   ⟨1, (44, 61), (44, 60)⟩,
   ⟨1, (44, 59), (44, 58)⟩,
   ⟨1, (44, 57), (44, 56)⟩,
   ⟨1, (44, 55), (44, 54)⟩,
   ⟨1, (44, 53), (44, 52)⟩,
   ⟨1, (44, 51), (44, 50)⟩,
   ⟨1, (44, 49), (44, 48)⟩,
   ⟨1, (44, 47), (44, 46)⟩,
   ⟨1, (44, 45), (44, 44)⟩,
   ⟨1, (44, 43), (44, 42)⟩,
   ⟨1, (44, 41), (44, 40)⟩,
   ⟨1, (44, 39), (44, 38)⟩,
   ⟨1, (44, 37), (44, 36)⟩,
   ⟨1, (44, 35), (44, 34)⟩,
   ⟨1, (44, 33), (44, 32)⟩,
   ⟨1, (44, 31), (44, 30)⟩,
   ⟨1, (44, 29), (44, 28)⟩,
   ⟨1, (44, 27), (44, 26)⟩,
   ⟨1, (44, 25), (44, 24)⟩,
   ⟨1, (44, 23), (44, 22)⟩,
   ⟨1, (44, 21), (44, 20)⟩,
   ⟨1, (44, 19), (44, 16)⟩,
   ⟨1, (44, 15), (44, 14)⟩,
   ⟨1, (44, 13), (44, 12)⟩,
   ⟨1, (44, 11), (44, 10)⟩,
   ⟨1, (44, 9), (44, 8)⟩,
   ⟨1, (44, 7), (44, 6)⟩,
   ⟨1, (44, 5), (44, 4)⟩,
   ⟨1, (44, 3), (44, 2)⟩,
   ⟨2, (54, 90), (53, 90)⟩,
   ⟨2, (56, 90), (55, 90)⟩,
   ⟨2, (58, 90), (57, 90)⟩,
   ⟨2, (60, 90), (59, 90)⟩,
   ⟨2, (64, 90), (61, 90)⟩,
   ⟨2, (66, 90), (65, 90)⟩,
   ⟨2, (68, 90), (67, 90)⟩,
   ⟨2, (70, 90), (69, 90)⟩,
   ⟨2, (72, 90), (71, 90)⟩,
   ⟨2, (74, 90), (73, 90)⟩,
   ⟨2, (76, 90), (75, 90)⟩,
   ⟨2, (78, 90), (77, 90)⟩]

def coreSlots (kind : Bool) : List Slot := if kind then andCoreSlots else orCoreSlots
def outerSlots (kind : Bool) : List Slot := if kind then andOuterSlots else orOuterSlots
def slots (kind : Bool) : List Slot := coreSlots kind ++ outerSlots kind
def positions (kind : Bool) (b : Signals) : List C := (slots kind).map fun s => s.position b
def canonicalBoxes (kind : Bool) (b : Signals) : Finset C := (positions kind b).toFinset

/-- The exact player state associated with a complete canonical box placement. -/
def canonical (kind : Bool) (b : Signals) : State 81 107 := ⟨hub, canonicalBoxes kind b⟩

-- These finite certificates inspect two endpoints of each of 108/78 explicitly listed slots.
set_option maxRecDepth 65536 in
private theorem slots_checked : ∀ kind : Bool, ((slots kind).all fun s =>
    reservedTest kind s.zero && reservedTest kind s.one &&
      !wallTest kind s.zero && !wallTest kind s.one) = true := by decide +kernel

private theorem slot_position_reserved (kind : Bool) (s : Slot) (hs : s ∈ slots kind)
    (b : Signals) :
    reservedTest kind (s.position b) = true := by
  have hh := List.all_eq_true.mp (slots_checked kind) s hs
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hh
  unfold Slot.position
  split
  · exact hh.1.1.2
  · exact hh.1.1.1

private theorem slot_position_floor (kind : Bool) (s : Slot) (hs : s ∈ slots kind) (b : Signals) :
    wallTest kind (s.position b) = false := by
  have hh := List.all_eq_true.mp (slots_checked kind) s hs
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hh
  unfold Slot.position
  split
  · exact hh.2
  · exact hh.1.2

theorem canonicalBoxes_reserved (kind : Bool) (b : Signals) : canonicalBoxes kind b ⊆ reserved kind := by
  intro p hp
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
  exact (mem_reserved kind _).mpr (slot_position_reserved kind s hs b)

theorem canonicalBoxes_floor (kind : Bool) (b : Signals) :
    Disjoint (canonicalBoxes kind b) (walls kind) := by
  apply Finset.disjoint_left.mpr
  intro p hp hw
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
  have hf := slot_position_floor kind s hs b
  rw [(mem_walls kind _).mp hw] at hf
  contradiction

-- All 16 kind/assignment combinations are checked only for duplicate physical positions.
set_option maxRecDepth 65536 in
private theorem positions_nodup (kind : Bool) (b : Signals) : (positions kind b).Nodup := by
  have hh : ∀ (k a b c : Bool), (positions k ⟨a,b,c⟩).Nodup := by decide +kernel
  exact hh kind b.left b.upper b.right

theorem canonicalBoxes_card (kind : Bool) (b : Signals) :
    (canonicalBoxes kind b).card = (slots kind).length := by
  change (positions kind b).toFinset.card = _
  rw [List.toFinset_card_of_nodup (positions_nodup kind b)]
  exact List.length_map (fun s : Slot => s.position b)

/-- The full tiles contain 108 AND boxes or 78 OR boxes. -/
theorem slots_length (kind : Bool) : (slots kind).length = if kind then 108 else 78 := by
  cases kind <;> decide +kernel

theorem canonical_valid (kind : Bool) (b : Signals) (goals : Finset C) :
    (canonical kind b).Valid (board kind goals) := by
  have hw : wallTest kind hub = false := by cases kind <;> decide +kernel
  have hr : reservedTest kind hub = false := by cases kind <;> decide +kernel
  refine ⟨?_, canonicalBoxes_floor kind b, ?_⟩
  · intro h
    rw [(mem_walls kind hub).mp h] at hw
    contradiction
  · intro h
    have hc := (mem_reserved kind hub).mp (canonicalBoxes_reserved kind b h)
    rw [hc] at hr
    contradiction

/-- Location of a fixed physical identity in a canonical state. -/
def position (kind : Bool) (b : Signals) (i : Fin (slots kind).length) : C :=
  ((slots kind).get i).position b

theorem position_injective (kind : Bool) (b : Signals) : Function.Injective (position kind b) := by
  intro i j he
  have hi : i.val < (positions kind b).length := by simpa only [positions, List.length_map] using i.isLt
  have hj : j.val < (positions kind b).length := by simpa only [positions, List.length_map] using j.isLt
  have hget : (positions kind b).get ⟨i.val, hi⟩ = (positions kind b).get ⟨j.val, hj⟩ := by
    simpa [positions, position, List.get_eq_getElem] using he
  have hh := (positions_nodup kind b).injective_get hget
  exact Fin.ext (congrArg (fun k : Fin (positions kind b).length => k.val) hh)

theorem position_image (kind : Bool) (b : Signals) :
    Finset.univ.image (position kind b) = canonicalBoxes kind b := by
  ext p
  simp only [canonicalBoxes, List.mem_toFinset, positions, List.mem_map,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(slots kind).get i, List.get_mem _ _, rfl⟩
  · rintro ⟨s, hs, he⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hs
    exact ⟨i, by simpa only [position, hi] using he⟩

/-- A complete physical indexing of every box in a canonical tile. -/
def labelled (kind : Bool) (b : Signals) : LabelledState (Fin (slots kind).length) 81 107 :=
  ⟨canonical kind b, position kind b, position_injective kind b, position_image kind b⟩

end PushPuzzle.PushFS.Gadgets.Gates
