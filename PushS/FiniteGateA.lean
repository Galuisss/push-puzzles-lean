/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateAStraight
public import PushS.FiniteGatePrepared
import Mathlib.Tactic.Tauto

/-! The full AND A branch, with exact tool sharing and explicit entry connections. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateA

set_option maxRecDepth 8192

open PushFS FiniteGeometry FiniteGateCore FiniteGateState FiniteGateMacros FiniteGatePrepared
open FiniteGateTools FiniteGateAStraight FiniteLineMacros

attribute [local irreducible] side

private theorem stage_zero (w : ℕ) (b c : Bool) :
    stage w b c 0 = andNormalPhases w false b c := by
  ext i <;> simp [stage, andNormalPhases]

private theorem stage_seven (w : ℕ) (b c : Bool) :
    stage w b c 7 = { andNormalPhases w true b c with triggerA := 1 } := by
  ext i <;> simp [stage, andNormalPhases]

theorem upper_source (w : ℕ) (b c : Bool) :
    upperPhases w (stage w b c 1) true = stage w b c 1 := by
  ext i <;> simp [upperPhases, stage, Function.update]
  tauto

theorem upper_target (w : ℕ) (b c : Bool) :
    upperPhases w (stage w b c 1) false = stage w b c 2 := by
  ext i <;> simp [upperPhases, stage, Function.update]
  tauto

theorem flip_source (w : ℕ) (b c : Bool) :
    flipPhases w (stage w b c 3) false = stage w b c 3 := by
  ext i <;> simp [flipPhases, stage, Function.update]
  by_cases hi : i.val = w+4
  · have he : i = ⟨w+4, by omega⟩ := Fin.ext hi
    simp [he]
  · have he : i ≠ ⟨w+4, by omega⟩ := fun h => hi (congrArg Fin.val h)
    simp [hi, he]

theorem flip_target (w : ℕ) (b c : Bool) :
    flipPhases w (stage w b c 3) true = stage w b c 4 := by
  ext i <;> simp [flipPhases, stage, Function.update]
  by_cases hi : i.val = w+4
  · have he : i = ⟨w+4, by omega⟩ := Fin.ext hi
    simp [he]
  · have he : i ≠ ⟨w+4, by omega⟩ := fun h => hi (congrArg Fin.val h)
    simp [hi, he]

theorem protection_source (w : ℕ) (b c : Bool) :
    protectionPhases w (stage w b c 5) false = stage w b c 5 := by
  ext i <;> simp [protectionPhases, stage, Function.update]
  by_cases hi : i.val = w+4
  · have he : i = ⟨w+4, by omega⟩ := Fin.ext hi
    simp [he]
  · have he : i ≠ ⟨w+4, by omega⟩ := fun h => hi (congrArg Fin.val h)
    simp [hi, he]

theorem protection_target (w : ℕ) (b c : Bool) :
    protectionPhases w (stage w b c 5) true = stage w b c 6 := by
  ext i <;> simp [protectionPhases, stage, Function.update]
  by_cases hi : i.val = w+4
  · have he : i = ⟨w+4, by omega⟩ := Fin.ext hi
    simp [he]
  · have he : i ≠ ⟨w+4, by omega⟩ := fun h => hi (congrArg Fin.val h)
    simp [hi, he]

theorem stage_zero_boxes (w : ℕ) (b c : Bool) :
    andMixedBoxes w (stage w b c 0) = andBoxes w false b c := by
  rw [stage_zero, andMixedBoxes_normal]

theorem stage_seven_boxes (w : ℕ) (hw : 2 ≤ w) (b c : Bool) :
    andMixedBoxes w (stage w b c 7) =
      insert (point w 3 0) ((andBoxes w true b c).erase (point w 2 0)) := by
  have he := Line.image_relocate (andCell w true b c)
    (andMixedCell w (stage w b c 7)) (andCell_injective w hw true b c) .triggerA (by
      intro l hl
      cases l with
      | triggerA => exact False.elim (hl rfl)
      | _ => simp [stage_seven, andMixedCell, andNormalPhases, andCell, andPoint])
  have hold : andMixedCell w (stage w b c 7) .triggerA = point w 3 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [andMixedCell, stage, point]
  have hnew : andCell w true b c .triggerA = point w 2 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]
  simpa only [andMixedBoxes, andBoxes, hold, hnew] using he.symm

private theorem stage_seven_prepared (w : ℕ) (hw : 2 ≤ w) (b : Bool) :
    andMixedBoxes w (stage w b false 7) = andPreparedBoxes w b := by
  have hold : andCell w false b false .triggerA = point w 3 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]
  have hnew : andCell w true b false .triggerA = point w 2 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]
  simpa only [andPreparedBoxes, hold, hnew] using stage_seven_boxes w hw b false

/-- The exact entry and exit cells of each placed A-branch tool. -/
def upperEntry (w : ℕ) := (upperEmbedding w).cells (FiniteTools.turnNode w .corner)
def upperExit (w : ℕ) := (upperEmbedding w).cells (FiniteTools.turnNode w .vertical1)
def upperReverseExit (w : ℕ) := (upperEmbedding w).cells (FiniteTools.turnNode w .horizontal0)
def flipEntry (w : ℕ) := (flipEmbedding w).cells (FiniteTools.flipNode w .rightSupport)
def flipExit (w : ℕ) := (flipEmbedding w).cells (FiniteTools.flipNode w .left0)
def flipReverseEntry (w : ℕ) := (flipEmbedding w).cells (FiniteTools.flipNode w .leftReverseSupport)
def flipReverseExit (w : ℕ) := (flipEmbedding w).cells (FiniteTools.flipNode w .right1)
def protectionEntry (w : ℕ) := (protectionEmbedding w).cells (FiniteTools.turnNode w .corner)
def protectionExit (w : ℕ) := (protectionEmbedding w).cells (FiniteTools.turnNode w .horizontal0)
def protectionReverseExit (w : ℕ) := (protectionEmbedding w).cells (FiniteTools.turnNode w .vertical1)

/-- Actual travel between the fixed entries of consecutive forward branch pieces. -/
structure ForwardConnections (w : ℕ) (b : Bool)
    (goals : Finset (Cell (side w) (side w))) : Prop where
  west_upper : Reachable (andBoard w goals) (some 1)
    ⟨(Segment.west.sweep w).hub, andMixedBoxes w (stage w b false 1)⟩
    ⟨upperEntry w, andMixedBoxes w (stage w b false 1)⟩
  upper_line : Reachable (andBoard w goals) (some 1)
    ⟨upperExit w, andMixedBoxes w (stage w b false 2)⟩
    ⟨(Segment.upper.sweep w).hub, andMixedBoxes w (stage w b false 2)⟩
  line_flip : Reachable (andBoard w goals) (some 1)
    ⟨(Segment.upper.sweep w).hub, andMixedBoxes w (stage w b false 3)⟩
    ⟨flipEntry w, andMixedBoxes w (stage w b false 3)⟩
  flip_line : Reachable (andBoard w goals) (some 1)
    ⟨flipExit w, andMixedBoxes w (stage w b false 4)⟩
    ⟨(Segment.lower.sweep w).hub, andMixedBoxes w (stage w b false 4)⟩
  line_protection : Reachable (andBoard w goals) (some 1)
    ⟨(Segment.lower.sweep w).hub, andMixedBoxes w (stage w b false 5)⟩
    ⟨protectionEntry w, andMixedBoxes w (stage w b false 5)⟩
  protection_line : Reachable (andBoard w goals) (some 1)
    ⟨protectionExit w, andMixedBoxes w (stage w b false 6)⟩
    ⟨(Segment.guard.sweep w).hub, andMixedBoxes w (stage w b false 6)⟩
  line_trigger : Reachable (andBoard w goals) (some 1)
    ⟨(Segment.guard.sweep w).hub, andMixedBoxes w (stage w b false 7)⟩
    ⟨point w (w+4) 1, andMixedBoxes w (stage w b false 7)⟩

/-- Propagate through the whole protection chain, both turns, the flip, and the final A push. -/
theorem and_A_forward (w : ℕ) (hw : 2 ≤ w) (b : Bool)
    (goals : Finset (Cell (side w) (side w))) (C : ForwardConnections w b goals) :
    Reachable (andBoard w goals) (some 1)
      ⟨(Segment.west.sweep w).hub, andBoxes w false b false⟩
      ⟨point w (w+4) 1, andBoxes w true b false⟩ := by
  have hW := Segment.forward w hw b false .west goals
  have hU := upper_backward w hw (stage w b false 1) goals
  rw [upper_source, upper_target] at hU
  have hUL := Segment.forward w hw b false .upper goals
  have hF := flip_forward w hw (stage w b false 3) goals
  rw [flip_source, flip_target] at hF
  have hLL := Segment.forward w hw b false .lower goals
  have hP := protection_forward w hw (stage w b false 5) goals
  rw [protection_source, protection_target] at hP
  have hG := Segment.forward w hw b false .guard goals
  have hA := and_A_left_prepared w hw b goals
  rw [← stage_seven_prepared w hw b] at hA
  have h1 := (hW.trans C.west_upper).trans hU
  have h2 := ((h1.trans C.upper_line).trans hUL).trans C.line_flip
  have h3 := ((h2.trans hF).trans C.flip_line).trans hLL
  have h4 := ((h3.trans C.line_protection).trans hP).trans C.protection_line
  have hr := ((h4.trans hG).trans C.line_trigger).trans hA
  simpa only [Segment.before, stage_zero_boxes] using hr

/-- Actual travel between the entries of consecutive reverse branch pieces. -/
structure BackwardConnections (w : ℕ) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) : Prop where
  line_protection : Reachable (andBoard w goals) (some 1)
    ⟨(Segment.guard.sweep w).hub, andMixedBoxes w (stage w b c 6)⟩
    ⟨protectionEntry w, andMixedBoxes w (stage w b c 6)⟩
  protection_line : Reachable (andBoard w goals) (some 1)
    ⟨protectionReverseExit w, andMixedBoxes w (stage w b c 5)⟩
    ⟨(Segment.lower.sweep w).hub, andMixedBoxes w (stage w b c 5)⟩
  line_flip : Reachable (andBoard w goals) (some 1)
    ⟨(Segment.lower.sweep w).hub, andMixedBoxes w (stage w b c 4)⟩
    ⟨flipReverseEntry w, andMixedBoxes w (stage w b c 4)⟩
  flip_line : Reachable (andBoard w goals) (some 1)
    ⟨flipReverseExit w, andMixedBoxes w (stage w b c 3)⟩
    ⟨(Segment.upper.sweep w).hub, andMixedBoxes w (stage w b c 3)⟩
  line_upper : Reachable (andBoard w goals) (some 1)
    ⟨(Segment.upper.sweep w).hub, andMixedBoxes w (stage w b c 2)⟩
    ⟨upperEntry w, andMixedBoxes w (stage w b c 2)⟩
  upper_line : Reachable (andBoard w goals) (some 1)
    ⟨upperReverseExit w, andMixedBoxes w (stage w b c 1)⟩
    ⟨(Segment.west.sweep w).hub, andMixedBoxes w (stage w b c 1)⟩

/-- Reverse the full A branch and restore every auxiliary box to the new normal state. -/
theorem and_A_backward (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) (C : BackwardConnections w b c goals) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w 1 1, andBoxes w true b c⟩
      ⟨(Segment.west.sweep w).hub, andBoxes w false b c⟩ := by
  have hA := and_A_right w hw b c goals
  rw [← stage_seven_boxes w hw b c] at hA
  have hG := Segment.backward w hw b c .guard goals
  have hP := protection_backward w hw (stage w b c 5) goals
  rw [protection_source, protection_target] at hP
  have hLL := Segment.backward w hw b c .lower goals
  have hF := flip_backward w hw (stage w b c 3) goals
  rw [flip_source, flip_target] at hF
  have hUL := Segment.backward w hw b c .upper goals
  have hU := upper_forward w hw (stage w b c 1) goals
  rw [upper_source, upper_target] at hU
  have hW := Segment.backward w hw b c .west goals
  have hguardHub : (Segment.guard.sweep w).hub = point w 1 1 := rfl
  rw [hguardHub] at hG
  have h1 := ((hA.trans hG).trans C.line_protection).trans hP
  have h2 := ((h1.trans C.protection_line).trans hLL).trans C.line_flip
  have h3 := ((h2.trans hF).trans C.flip_line).trans hUL
  have h4 := ((h3.trans C.line_upper).trans hU).trans C.upper_line
  have hr := h4.trans hW
  simpa only [Segment.before, stage_zero_boxes] using hr

end PushPuzzle.PushS.FiniteGateA
