/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ForwardControl
import Mathlib.Data.List.GetD

/-! The three actual room interactions implementing one original self-closing-door traversal. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

/-- The original door-list channel number. -/
def tunnelIndex (i : ℕ) (bit : Bool) : ℕ := 2 * i + if bit then 1 else 0

theorem tunnelIndex_div (i : ℕ) (bit : Bool) : tunnelIndex i bit / 2 = i := by
  cases bit <;> dsimp [tunnelIndex] <;> omega

theorem tunnelIndex_bit (i : ℕ) (bit : Bool) : channelBit (tunnelIndex i bit) = bit := by
  cases bit <;> simp [channelBit, tunnelIndex, Nat.add_mod]

theorem tunnelIndex_lt (I : Instance) (i : Fin I.doors.length) (bit : Bool) :
    tunnelIndex i.val bit < 2 * I.doors.length := by
  have hi := i.isLt
  cases bit <;> dsimp [tunnelIndex] <;> omega

theorem channel_tunnelIndex (I : Instance) (i : Fin I.doors.length) (bit : Bool) :
    channel I (tunnelIndex i.val bit) = I.doors[i].tunnel bit := by
  unfold channel
  rw [tunnelIndex_div, tunnelIndex_bit, List.getD_eq_getElem _ _ i.isLt]
  rfl

/-- The check slot for the selected directed channel. -/
def checkRegister (bit : Bool) : Register := if bit then .checkB else .checkA

/-- The temporary slot reached through the first internal return wire. -/
private def temporaryRegister (bit : Bool) : Register := if bit then .low else .high

private def firstOutput (bit : Bool) : ℕ := if bit then 51 else 39
private def secondOutput (bit : Bool) : ℕ := if bit then 11 else 79
private def finalOutput (bit : Bool) : ℕ := if bit then 29 else 61

private theorem collision_first (bit : Bool) : collisionRow (Register.stable bit) (checkRegister bit) = firstOutput bit := by
  cases bit <;> rfl

private theorem collision_second (bit : Bool) : collisionRow (checkRegister bit) (temporaryRegister bit) = secondOutput bit := by
  cases bit <;> rfl

private theorem collision_final (bit : Bool) : collisionRow (temporaryRegister bit) (Register.stable (!bit)) = finalOutput bit := by
  cases bit <;> rfl

private theorem firstWire_mem (storage : Bool) (I : Instance) (i : Fin I.doors.length) (bit : Bool) :
    (⟨doorBase i.val + firstOutput bit, bit,
      doorBase i.val + (temporaryRegister bit).row, !bit⟩ : Wire) ∈ (layout storage I).wires := by
  apply internal_mem_wires storage I
  apply List.mem_flatMap.mpr
  refine ⟨i.val, List.mem_range.mpr i.isLt, ?_⟩
  cases bit <;> simp [firstOutput, temporaryRegister, Register.row]

private theorem secondWire_mem (storage : Bool) (I : Instance) (i : Fin I.doors.length) (bit : Bool) :
    (⟨doorBase i.val + secondOutput bit, bit,
      doorBase i.val + (Register.stable (!bit)).row, bit⟩ : Wire) ∈ (layout storage I).wires := by
  apply internal_mem_wires storage I
  apply List.mem_flatMap.mpr
  refine ⟨i.val, List.mem_range.mpr i.isLt, ?_⟩
  cases bit <;> simp [secondOutput, Register.stable, Register.row]

private theorem arrivalWire_mem (storage : Bool) (I : Instance) (i : Fin I.doors.length) (bit : Bool) :
    (⟨doorBase i.val + finalOutput bit, !bit,
      inputRow I (rank I (I.doors[i].tunnel bit).target) 0 (tunnelIndex i.val bit), true⟩ : Wire) ∈
      (layout storage I).wires := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨tunnelIndex i.val bit, List.mem_range.mpr (tunnelIndex_lt I i bit), ?_⟩
  simp only [arrivalWire, tunnelIndex_div, tunnelIndex_bit, channel_tunnelIndex]
  cases bit <;> rfl

namespace Stock

variable {I : Instance}

/-- Three collisions and their three actual wires flip the selected original door. -/
theorem call (storage : Bool) (S : Stock I) (hwire : WireSimulation storage I)
    (i : Fin I.doors.length) (bit : Bool) (hregister : S.register i = Register.stable bit)
    (hsignal : S.signal = atRow storage I (doorBase i.val + (checkRegister bit).row)) :
    Finite.Reachable 1 (S.canonical storage)
      (({(S.setRegister i (Register.stable (!bit))) with
        signal := atRow storage I (inputRow I (rank I (I.doors[i].tunnel bit).target)
          0 (tunnelIndex i.val bit))} : Stock I).canonical storage) := by
  let first : Stock I := {(S.setRegister i (checkRegister bit)) with
    signal := atRow storage I (doorBase i.val + firstOutput bit)}
  have hne1 : S.register i ≠ checkRegister bit := by rw [hregister]; cases bit <;> decide
  have hc1 : Finite.Reachable 1 (S.canonical storage) (first.canonical storage) := by
    have hr := S.collide storage i (checkRegister bit) hne1 hsignal
    simpa only [first, hregister, collision_first, atRow] using hr
  let second : Stock I := {first with
    signal := atRow storage I (doorBase i.val + (temporaryRegister bit).row)}
  have hfirst : first.register i = checkRegister bit := by simp [first, setRegister]
  have hne2 : first.register i ≠ temporaryRegister bit := by rw [hfirst]; cases bit <;> decide
  have hw1 : Finite.Reachable 1 (first.canonical storage) (second.canonical storage) :=
    hwire first ⟨doorBase i.val + firstOutput bit, bit,
      doorBase i.val + (temporaryRegister bit).row, !bit⟩
      (firstWire_mem storage I i bit) rfl (first.door_input_ready storage i _ hne2)
  let third : Stock I := {(second.setRegister i (temporaryRegister bit)) with
    signal := atRow storage I (doorBase i.val + secondOutput bit)}
  have hsecond : second.register i = checkRegister bit := hfirst
  have hc2 : Finite.Reachable 1 (second.canonical storage) (third.canonical storage) := by
    have hr := second.collide storage i (temporaryRegister bit) hne2 rfl
    simpa only [third, hsecond, collision_second, atRow] using hr
  let fourth : Stock I := {third with
    signal := atRow storage I (doorBase i.val + (Register.stable (!bit)).row)}
  have hthird : third.register i = temporaryRegister bit := by simp [third, setRegister]
  have hne3 : third.register i ≠ Register.stable (!bit) := by rw [hthird]; cases bit <;> decide
  have hw2 : Finite.Reachable 1 (third.canonical storage) (fourth.canonical storage) :=
    hwire third ⟨doorBase i.val + secondOutput bit, bit,
      doorBase i.val + (Register.stable (!bit)).row, bit⟩
      (secondWire_mem storage I i bit) rfl (third.door_input_ready storage i _ hne3)
  let fifth : Stock I := {(fourth.setRegister i (Register.stable (!bit))) with
    signal := atRow storage I (doorBase i.val + finalOutput bit)}
  have hfourth : fourth.register i = temporaryRegister bit := hthird
  have hc3 : Finite.Reachable 1 (fourth.canonical storage) (fifth.canonical storage) := by
    have hr := fourth.collide storage i (Register.stable (!bit)) hne3 rfl
    simpa only [fifth, hfourth, collision_final, atRow] using hr
  let final : Stock I := {fifth with
    signal := atRow storage I (inputRow I (rank I (I.doors[i].tunnel bit).target) 0 (tunnelIndex i.val bit))}
  have hw3 : Finite.Reachable 1 (fifth.canonical storage) (final.canonical storage) :=
    hwire fifth ⟨doorBase i.val + finalOutput bit, !bit,
      inputRow I (rank I (I.doors[i].tunnel bit).target) 0 (tunnelIndex i.val bit), true⟩
      (arrivalWire_mem storage I i bit) rfl (fifth.junction_input_ready storage _ _ _)
  have hfinal : final = ({(S.setRegister i (Register.stable (!bit))) with
      signal := atRow storage I (inputRow I (rank I (I.doors[i].tunnel bit).target) 0 (tunnelIndex i.val bit))} : Stock I) := by
    apply eq_of_register_signal
    · simp [final, fifth, fourth, third, second, first, setRegister, Function.update_idem]
    · rfl
  rw [← hfinal]
  exact hc1.trans (hw1.trans (hc2.trans (hw2.trans (hc3.trans hw3))))

end Stock
end PushPuzzle.PushPush.Doors.Source
