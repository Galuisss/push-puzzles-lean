/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.CompilerInstance
public import PushPush.Doors.Room

/-! Complete physical inventory: one register box per door and one travelling signal. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors

/-- The six door slots and the common terminal erasure slot. -/
inductive Register
  | low | a | checkA | checkB | b | erase | high
  deriving DecidableEq

namespace Register

/-- Relative row in the original ninety-row chamber. -/
def row : Register → ℕ
  | .low => 10
  | .a => 30
  | .checkA => 40
  | .checkB => 50
  | .b => 60
  | .erase => 70
  | .high => 80

/-- Embed the ordinary six-slot room into its storage extension. -/
def ofSlot : Room.Slot → Register
  | .low => .low
  | .a => .a
  | .checkA => .checkA
  | .checkB => .checkB
  | .b => .b
  | .high => .high

@[simp] theorem row_ofSlot (slot : Room.Slot) : (ofSlot slot).row = slot.row := by
  cases slot <;> rfl

/-- A stable source bit is stored at A or B. -/
def stable (bit : Bool) : Register := if bit then .b else .a

@[simp] theorem row_stable (bit : Bool) : (stable bit).row = if bit then 60 else 30 := by
  cases bit <;> rfl

@[simp] theorem ofSlot_stable (bit : Bool) : ofSlot (Room.stable bit) = stable bit := by
  cases bit <;> rfl

theorem row_bounds (r : Register) : 10 ≤ r.row ∧ r.row ≤ 80 := by cases r <;> decide

theorem row_injective : Function.Injective row := by
  intro first second he
  cases first <;> cases second <;> simp_all [row]

end Register

namespace Source

/-- Door-register inventory and the absolute coordinate of the unique active signal. -/
structure Stock (I : Instance) where
  /-- Physical stored slot in each original door chamber. -/
  register : Fin I.doors.length → Register
  /-- The signal's physical coordinate, including the common vertical translation. -/
  signal : ℕ × ℕ

namespace Stock

variable {I : Instance}

/-- All original door boxes, with their chamber identities retained. -/
def registerPoints (storage : Bool) (S : Stock I) : Finset (ℕ × ℕ) :=
  Finset.univ.image fun i : Fin I.doors.length =>
    ((layout storage I).rackX - 1, doorBase i.val + (S.register i).row + (layout storage I).shift)

/-- The complete unlabelled box set before finite rasterization. -/
def rawBoxes (storage : Bool) (S : Stock I) : Finset (ℕ × ℕ) :=
  (layout storage I).fixed ∪ S.registerPoints storage ∪ {S.signal}

/-- The real finite box inventory. -/
def boxes (storage : Bool) (S : Stock I) :
    Finset (PushFS.Cell (layout storage I).width (layout storage I).height) :=
  (layout storage I).raster (S.rawBoxes storage)

/-- A real state has exactly this complete inventory; its player position is retained. -/
def Realizes (storage : Bool) (S : Stock I)
    (s : PushFS.State (layout storage I).width (layout storage I).height) : Prop :=
  s.boxes = S.boxes storage

/-- The canonical exterior player position for the same physical stock. -/
def canonical (storage : Bool) (S : Stock I) :
    PushFS.State (layout storage I).width (layout storage I).height :=
  ⟨(layout storage I).corner, S.boxes storage⟩

@[simp] theorem canonical_realizes (storage : Bool) (S : Stock I) :
    S.Realizes storage (S.canonical storage) := rfl

/-- The complete initial source inventory. -/
def initial (storage : Bool) (I : Instance) : Stock I where
  register := fun i => Register.stable I.doors[i].initial
  signal := ((layout storage I).rackX - 1, (layout storage I).launch + (layout storage I).shift)

/-- Stable inventory for any explicit source register bit list. -/
def ofBits (I : Instance) (bits : List Bool) (signal : ℕ × ℕ) : Stock I where
  register := fun i => Register.stable (bits.getD i.val false)
  signal := signal

/-- All door values have been erased after the storage cleanup. -/
def terminal (storage : Bool) (I : Instance) : Stock I where
  register := if storage then fun _ => .erase else (initial storage I).register
  signal := ((layout storage I).rackX - 1, (layout storage I).stop + (layout storage I).shift)

theorem initial_registerPoints (storage : Bool) (I : Instance) :
    (initial storage I).registerPoints storage =
      ((dataRows I).map fun y => ((layout storage I).rackX - 1, y + (layout storage I).shift)).toFinset := by
  ext p
  simp only [registerPoints, Finset.mem_image, Finset.mem_univ, true_and,
    List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨doorBase i.val + if I.doors[i].initial then 60 else 30, ?_, ?_⟩
    · apply List.mem_map.mpr
      refine ⟨(I.doors[i], i.val), ?_, rfl⟩
      apply List.mk_mem_zipIdx_iff_getElem?.mpr
      simp [i.isLt]
    · simp [initial]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, rfl⟩ := dataRows_mem I hy
    refine ⟨i, ?_⟩
    simp [initial]

private theorem initial_rawBoxes (storage : Bool) (I : Instance) :
    (initial storage I).rawBoxes storage = (layout storage I).initialRaw := by
  rw [rawBoxes, initial_registerPoints]
  ext p
  simp only [Layout.initialRaw, List.map_cons, List.toFinset_cons, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_insert]
  tauto

theorem initial_canonical (storage : Bool) (I : Instance) :
    (initial storage I).canonical storage = (puzzle storage I).initial := by
  change (PushFS.State.mk (layout storage I).corner
    ((layout storage I).raster ((initial storage I).rawBoxes storage))) =
      PushFS.State.mk (layout storage I).corner ((layout storage I).raster (layout storage I).initialRaw)
  rw [initial_rawBoxes]

end Stock
end Source
end PushPuzzle.PushPush.Doors
