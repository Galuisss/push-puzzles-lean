/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.MachineState
public import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-! Exact single-register updates of complete physical stocks. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source.Stock

variable {I : Instance}

theorem eq_of_register_signal {S T : Stock I} (hr : S.register = T.register)
    (hs : S.signal = T.signal) : S = T := by
  cases S
  cases T
  cases hr
  cases hs
  rfl

/-- The absolute physical coordinate of one original door's register box. -/
def registerPoint (storage : Bool) (S : Stock I) (i : Fin I.doors.length) : ℕ × ℕ :=
  ((layout storage I).rackX - 1, doorBase i.val + (S.register i).row + (layout storage I).shift)

/-- A stored slot change preserves the signal and every other original door. -/
def setRegister (S : Stock I) (i : Fin I.doors.length) (value : Register) : Stock I :=
  {S with register := Function.update S.register i value}

private theorem registerPoint_owner (storage : Bool) (S T : Stock I)
    {i j : Fin I.doors.length} (he : S.registerPoint storage i = T.registerPoint storage j) :
    i = j := by
  have hi := Register.row_bounds (S.register i)
  have hj := Register.row_bounds (T.register j)
  have hy := congrArg Prod.snd he
  change doorBase i.val + (S.register i).row + (layout storage I).shift =
    doorBase j.val + (T.register j).row + (layout storage I).shift at hy
  apply Fin.ext
  unfold doorBase at hy
  omega

theorem registerPoint_injective (storage : Bool) (S : Stock I) :
    Function.Injective (S.registerPoint storage) :=
  fun _ _ he => registerPoint_owner storage S S he

@[simp] theorem registerPoint_mem (storage : Bool) (S : Stock I) (i : Fin I.doors.length) :
    S.registerPoint storage i ∈ S.registerPoints storage :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

@[simp] theorem registerPoint_setRegister_self (storage : Bool) (S : Stock I)
    (i : Fin I.doors.length) (value : Register) :
    (S.setRegister i value).registerPoint storage i =
      ((layout storage I).rackX - 1, doorBase i.val + value.row + (layout storage I).shift) := by
  simp [registerPoint, setRegister]

private theorem registerPoint_setRegister_ne (storage : Bool) (S : Stock I)
    (i j : Fin I.doors.length) (value : Register) (hji : j ≠ i) :
    (S.setRegister i value).registerPoint storage j = S.registerPoint storage j := by
  simp only [registerPoint, setRegister, Function.update_of_ne hji]

/-- Updating a register erases precisely its old point and inserts precisely its new point. -/
theorem registerPoints_setRegister (storage : Bool) (S : Stock I)
    (i : Fin I.doors.length) (value : Register) :
    (S.setRegister i value).registerPoints storage =
      insert ((layout storage I).rackX - 1,
        doorBase i.val + value.row + (layout storage I).shift)
        ((S.registerPoints storage).erase (S.registerPoint storage i)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨j, _, he⟩ := Finset.mem_image.mp hp
    change (S.setRegister i value).registerPoint storage j = p at he
    by_cases hji : j = i
    · subst j
      apply Finset.mem_insert.mpr
      apply Or.inl
      simpa only [registerPoint_setRegister_self] using he.symm
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_erase.mpr
      rw [registerPoint_setRegister_ne storage S i j value hji] at he
      refine ⟨?_, he ▸ registerPoint_mem storage S j⟩
      intro hpi
      exact hji (registerPoint_injective storage S (he.trans hpi))
  · intro hp
    rcases Finset.mem_insert.mp hp with he | hp
    · exact he ▸ (registerPoint_setRegister_self storage S i value ▸
        registerPoint_mem storage (S.setRegister i value) i)
    · obtain ⟨hpi, hp⟩ := Finset.mem_erase.mp hp
      obtain ⟨j, _, he⟩ := Finset.mem_image.mp hp
      have hji : j ≠ i := by
        intro hji
        subst j
        exact hpi he.symm
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _,
        (registerPoint_setRegister_ne storage S i j value hji).trans he⟩

/-- Updating a source bit changes exactly its own physical stable register. -/
theorem ofBits_set (I : Instance) (bits : List Bool) (signal : ℕ × ℕ)
    (hlen : bits.length = I.doors.length) (i : Fin I.doors.length) (value : Bool) :
    ofBits I (bits.set i.val value) signal =
      (ofBits I bits signal).setRegister i (Register.stable value) := by
  have hreg : (ofBits I (bits.set i.val value) signal).register =
      ((ofBits I bits signal).setRegister i (Register.stable value)).register := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [ofBits, setRegister, Function.update_self]
      rw [List.getD_set_self (by omega)]
    · have hval : j.val ≠ i.val := fun he => hji (Fin.ext he)
      simp only [ofBits, setRegister, Function.update_of_ne hji]
      rw [List.getD_set_ne hval.symm]
  exact eq_of_register_signal hreg rfl

@[simp] theorem ofBits_initial_register (I : Instance) (signal : ℕ × ℕ)
    (i : Fin I.doors.length) :
    (ofBits I I.initial.bits signal).register i = Register.stable I.doors[i].initial := by
  change Register.stable ((I.doors.map Cslib.Complexity.SelfClosingDoor.Door.initial).getD i.val false) = _
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map]
  rfl

theorem ofBits_initial (storage : Bool) (I : Instance) :
    ofBits I I.initial.bits (initial storage I).signal = initial storage I := by
  apply eq_of_register_signal
  · funext i
    exact ofBits_initial_register I _ i
  · rfl

private theorem terminal_registerPoints (storage : Bool) (I : Instance) :
    (terminal storage I).registerPoints storage =
      ((layout storage I).goalRows.map fun y =>
        ((layout storage I).rackX - 1, y + (layout storage I).shift)).toFinset := by
  cases storage
  · exact initial_registerPoints false I
  · ext p
    constructor
    · intro hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      apply List.mem_toFinset.mpr
      apply List.mem_map.mpr
      refine ⟨doorBase i.val + 70, ?_, rfl⟩
      exact List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩
    · intro hp
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
      exact Finset.mem_image.mpr ⟨⟨i, List.mem_range.mp hi⟩, Finset.mem_univ _, rfl⟩

private theorem terminal_rawBoxes (storage : Bool) (I : Instance) :
    (terminal storage I).rawBoxes storage = (layout storage I).goalsRaw := by
  rw [rawBoxes, terminal_registerPoints]
  ext p
  simp only [Layout.goalsRaw, List.map_cons, List.toFinset_cons, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_insert]
  tauto

/-- The common erased terminal inventory is exactly the actual storage goal set. -/
theorem terminal_boxes (storage : Bool) (I : Instance) :
    (terminal storage I).boxes storage = (puzzle storage I).board.goals := by
  change (layout storage I).raster ((terminal storage I).rawBoxes storage) =
    (layout storage I).raster (layout storage I).goalsRaw
  rw [terminal_rawBoxes]

end PushPuzzle.PushPush.Doors.Source.Stock
