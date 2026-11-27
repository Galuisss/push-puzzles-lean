/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerInternal
public import PushS.PortLayoutPolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership

/-! Standard unary machine implementations of the literal ear and one gate-buffer operation. -/

public section
namespace PushPuzzle.Push.Partner

open PushS Turing.MultiTapeTM
open scoped PushPuzzle.PushS

/-- Unary layouts and the complete unary table of original-port positions. -/
enc_structure encBufferState : BufferState where
  layout : encPortLayout, ports : (encList encUnary)

/-- Unary endpoint-pair encoding used throughout the actual layout tables. -/
abbrev encPortPair : (ℕ × ℕ) ↪ List Bool := encPair encUnary encUnary

@[fun_prop] theorem shift_polyTime : ComputableInPolyTime
    (fun p : ℕ × ℕ => shift p.1 p.2) (encPair encUnary encUnary) encUnary := by
  unfold shift
  fun_prop

@[fun_prop] theorem sortPair_polyTime : ComputableInPolyTime
    (fun p : ℕ × ℕ => sortPair p.1 p.2) encPortPair encPortPair := by
  unfold sortPair encPortPair
  fun_prop

@[fun_prop] theorem mapPair_polyTime : ComputableInPolyTime
    (fun p : ℕ × (ℕ × ℕ) => mapPair p.1 p.2) (encPair encUnary encPortPair) encPortPair := by
  unfold mapPair encPortPair
  fun_prop

@[fun_prop] theorem mapGroup_polyTime : ComputableInPolyTime
    (fun p : ℕ × LowerGroup => mapGroup p.1 p.2) (encPair encUnary encLowerGroup) encLowerGroup := by
  have h := encLowerGroup_elim_polyTime (encP := encUnary) (encE := encLowerGroup)
    (g0 := fun p => .wire (shift p.1 p.2.1) (shift p.1 p.2.2))
    (g1 := fun p => .gate p.2.1 (shift p.1 p.2.2)) (by fun_prop) (by fun_prop)
  exact h.of_enc_eq (by intro p; rcases p with ⟨cut, g⟩; cases g <;> rfl)

@[local fun_prop] private theorem erase_polyTime {α : Type} [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × α => p.1.erase p.2)
      (encPair (encList enc) enc) (encList enc) := by
  have h : ComputableInPolyTime
      (fun p : List α × α => p.1.take (p.1.idxOf p.2) ++ p.1.drop (p.1.idxOf p.2 + 1))
      (encPair (encList enc) enc) (encList enc) := by fun_prop
  apply h.of_enc_eq
  intro p
  apply congrArg (encList enc)
  rw [List.erase_eq_eraseIdx_of_idxOf rfl, List.eraseIdx_eq_take_drop_succ]

/-- Every raw ear input has the literal standard polynomial-time layout output. -/
@[fun_prop] theorem ear_polyTime : ComputableInPolyTime
    (fun p : PortLayout × ℕ × (ℕ × ℕ) => ear p.1 p.2.1 p.2.2)
    (encPair encPortLayout (encPair encUnary encPortPair)) encPortLayout := by
  unfold ear
  fun_prop

namespace BufferState

@[fun_prop] theorem start_polyTime : ComputableInPolyTime start encPortLayout encBufferState := by
  unfold start
  fun_prop

@[fun_prop] theorem port_polyTime : ComputableInPolyTime
    (fun p : BufferState × ℕ => p.1.port p.2) (encPair encBufferState encUnary) encUnary := by
  unfold port
  fun_prop

@[fun_prop] theorem insertEar_polyTime : ComputableInPolyTime
    (fun p : BufferState × ℕ × (ℕ × ℕ) => p.1.insertEar p.2.1 p.2.2)
    (encPair encBufferState (encPair encUnary encPortPair)) encBufferState := by
  unfold insertEar
  fun_prop

@[fun_prop] theorem gateTest_polyTime : ComputableInPolyTime
    (fun p : PortLayout × ℕ => gateTest p.1 p.2) (encPair encPortLayout encUnary) encBool := by
  have htest : ComputableInPolyTime
      (fun p : ℕ × LowerGroup => match p.2 with
        | .wire .. => false
        | .gate _ first => decide (first = p.1)) (encPair encUnary encLowerGroup) encBool := by
    have h := encLowerGroup_elim_polyTime (encP := encUnary) (encE := encBool)
      (g0 := fun _ => false) (g1 := fun p => decide (p.2.2 = p.1)) (by fun_prop) (by fun_prop)
    exact h.of_enc_eq (by intro p; rcases p with ⟨first, g⟩; cases g <;> rfl)
  unfold gateTest
  apply ComputableInPolyTime.anyWithInput
  · fun_prop
  · have hp : ComputableInPolyTime
        (fun p : (PortLayout × ℕ) × LowerGroup => (p.1.2, p.2))
        (encPair (encPair encPortLayout encUnary) encLowerGroup) (encPair encUnary encLowerGroup) := by
      fun_prop
    exact (htest.comp hp).of_enc_eq (by intro p; rcases p with ⟨_, g⟩; cases g <;> rfl)

/-- One actual conditional gate inspection and optional ear insertion is total polynomial-time. -/
@[fun_prop] theorem bufferAt_polyTime : ComputableInPolyTime
    (fun p : BufferState × ℕ => p.1.bufferAt p.2) (encPair encBufferState encUnary) encBufferState := by
  unfold bufferAt
  fun_prop

end BufferState
end PushPuzzle.Push.Partner
