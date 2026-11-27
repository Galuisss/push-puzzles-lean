/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateAApproaches
public import PushS.FiniteGateBTemporary

/-! A uniform physical contract for every legal single-port AND/OR transition. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateForwardContract

open PushFS
open PushFS.Gadgets
open FiniteGeometry FiniteGateCore FiniteGateMacros FiniteGateInputs FiniteGateOutputs
open FiniteGateOutputReturn FiniteGateVertical FiniteGateBTriggers FiniteGateBForward FiniteGateBTemporary
open FiniteGateState FiniteGateAStraight FiniteGateAApproaches

/-- A complete physical macro with named endpoints in the specified interface set. -/
structure Macro {W H : ℕ} (B : Board W H) (initial final portals : Finset (Cell W H)) where
  entry : Cell W H
  exit : Cell W H
  entry_mem : entry ∈ portals
  exit_mem : exit ∈ portals
  run : Reachable B (some 1) ⟨entry, initial⟩ ⟨exit, final⟩

/-- Six actual single-port macro families, under the gate's ordinary legality relation. -/
structure Contract {W H : ℕ} (kind : Bool) (B : Board W H)
    (normal : Gates.Signals → Finset (Cell W H)) (portals : Finset (Cell W H)) : Prop where
  left_forward : ∀ b c, Gates.legal kind ⟨false,b,c⟩ → Gates.legal kind ⟨true,b,c⟩ →
    Nonempty (Macro B (normal ⟨false,b,c⟩) (normal ⟨true,b,c⟩) portals)
  left_backward : ∀ b c, Gates.legal kind ⟨true,b,c⟩ → Gates.legal kind ⟨false,b,c⟩ →
    Nonempty (Macro B (normal ⟨true,b,c⟩) (normal ⟨false,b,c⟩) portals)
  upper_forward : ∀ a c, Gates.legal kind ⟨a,false,c⟩ → Gates.legal kind ⟨a,true,c⟩ →
    Nonempty (Macro B (normal ⟨a,false,c⟩) (normal ⟨a,true,c⟩) portals)
  upper_backward : ∀ a c, Gates.legal kind ⟨a,true,c⟩ → Gates.legal kind ⟨a,false,c⟩ →
    Nonempty (Macro B (normal ⟨a,true,c⟩) (normal ⟨a,false,c⟩) portals)
  right_forward : ∀ a b, Gates.legal kind ⟨a,b,false⟩ → Gates.legal kind ⟨a,b,true⟩ →
    Nonempty (Macro B (normal ⟨a,b,false⟩) (normal ⟨a,b,true⟩) portals)
  right_backward : ∀ a b, Gates.legal kind ⟨a,b,true⟩ → Gates.legal kind ⟨a,b,false⟩ →
    Nonempty (Macro B (normal ⟨a,b,true⟩) (normal ⟨a,b,false⟩) portals)

/-- A legal NCL port flip gives an actual single-box macro with the complete normal inventories. -/
theorem Contract.canonical_step {W H : ℕ} {kind : Bool} {B : Board W H}
    {normal : Gates.Signals → Finset (Cell W H)} {portals : Finset (Cell W H)}
    (C : Contract kind B normal portals) (initial final : Gates.Signals)
    (hi : Gates.legal kind initial) (hf : Gates.legal kind final)
    (hs : Gates.singleChange initial final) :
    Nonempty (Macro B (normal initial) (normal final) portals) := by
  obtain ⟨a0,b0,c0⟩ := initial
  obtain ⟨a1,b1,c1⟩ := final
  rcases hs with ⟨hne, rfl, rfl⟩ | ⟨rfl, hne, rfl⟩ | ⟨rfl, rfl, hne⟩
  · cases a0 <;> cases a1 <;> first
      | exact False.elim (hne rfl)
      | exact C.left_forward _ _ hi hf
      | exact C.left_backward _ _ hi hf
  · cases b0 <;> cases b1 <;> first
      | exact False.elim (hne rfl)
      | exact C.upper_forward _ _ hi hf
      | exact C.upper_backward _ _ hi hf
  · cases c0 <;> cases c1 <;> first
      | exact False.elim (hne rfl)
      | exact C.right_forward _ _ hi hf
      | exact C.right_backward _ _ hi hf

def andPortals (w : ℕ) : Finset (Cell (side w) (side w)) :=
  {(Segment.west.sweep w).hub, point w 1 1, point w 2 2, point w 2 1,
    point w 3 1, point w (w+4) 1, point w (w+6) 1}

def orPortals (w : ℕ) : Finset (Cell (side w) (side w)) :=
  {point w 1 1, point w 3 2, point w 3 1, point w 4 1, point w (w+5) 1, point w (w+7) 1}

/-- The four remaining outer-face transfers used by complete AND gate macros. -/
structure AndConnections (w : ℕ) (goals : Finset (Cell (side w) (side w))) : Prop where
  left : ∀ b, Reachable (andBoard w goals) (some 1)
    ⟨(Segment.guard.sweep w).hub, andMixedBoxes w (stage w b false 7)⟩
    ⟨point w (w+4) 1, andMixedBoxes w (stage w b false 7)⟩
  upper_open : Reachable (andBoard w goals) (some 1)
    ⟨point w 2 2, andBBoxes w true false true⟩ ⟨point w (w+4) 1, andBBoxes w true false true⟩
  upper_closed : Reachable (andBoard w goals) (some 1)
    ⟨point w 2 1, temporaryBoxes w⟩ ⟨point w (w+4) 1, temporaryBoxes w⟩
  right : Reachable (andBoard w goals) (some 1)
    ⟨point w (w+6) 1, andOutputBoxes w true true false⟩
    ⟨point w 3 1, andOutputBoxes w true true false⟩

/-- The remaining outer-face transfers used by complete OR gate macros. -/
structure OrConnections (w : ℕ) (goals : Finset (Cell (side w) (side w))) : Prop where
  left : Reachable (orBoard w goals) (some 1)
    ⟨point w 1 1, orInputBoxes w false false true⟩
    ⟨point w (w+5) 1, orInputBoxes w false false true⟩
  upper : Reachable (orBoard w goals) (some 1)
    ⟨point w 3 2, orBBoxes w false false true⟩ ⟨point w (w+5) 1, orBBoxes w false false true⟩
  right_A : ∀ b, Reachable (orBoard w goals) (some 1)
    ⟨point w (w+7) 1, orOutputBoxes w true b false⟩ ⟨point w 3 1, orOutputBoxes w true b false⟩
  right_B : Reachable (orBoard w goals) (some 1)
    ⟨point w (w+7) 1, orOutputBoxes w false true false⟩
    ⟨point w 4 1, orOutputBoxes w false true false⟩

private theorem and_left_closed (b c : Bool) (h : Gates.legal true ⟨false,b,c⟩) : c = false := by
  cases c <;> simp [Gates.legal] at h ⊢

private theorem and_upper_closed (a c : Bool) (h : Gates.legal true ⟨a,false,c⟩) : c = false := by
  cases c <;> simp [Gates.legal] at h ⊢

private theorem or_both_closed (c : Bool) (h : Gates.legal false ⟨false,false,c⟩) : c = false := by
  cases c <;> simp [Gates.legal] at h ⊢

/-- Assemble all six AND port macros into the uniform physical contract. -/
theorem andContract (w : ℕ) (hw : 2 ≤ w) (goals : Finset (Cell (side w) (side w)))
    (C : AndConnections w goals) :
    Contract true (andBoard w goals) (fun s => andBoxes w s.left s.upper s.right) (andPortals w) := by
  constructor
  · intro b c hi _
    have hc := and_left_closed b c hi
    subst c
    exact ⟨⟨_, _, by simp [andPortals], by simp [andPortals],
      and_A_forward_local w hw b goals (C.left b)⟩⟩
  · intro b c _ _
    exact ⟨⟨_, _, by simp [andPortals], by simp [andPortals], and_A_backward_local w hw b c goals⟩⟩
  · intro a c hi _
    have hc := and_upper_closed a c hi
    subst c
    cases a with
    | false => exact ⟨⟨_, _, by simp [andPortals], by simp [andPortals],
        and_B_forward_closedA w hw goals C.upper_closed⟩⟩
    | true => exact ⟨⟨_, _, by simp [andPortals], by simp [andPortals],
        and_B_forward_openA w hw goals C.upper_open⟩⟩
  · intro a c _ _
    exact ⟨⟨_, _, by simp [andPortals], by simp [andPortals], and_B_backward w hw a c goals⟩⟩
  · intro a b _ _
    exact ⟨⟨_, _, by simp [andPortals], by simp [andPortals], and_C_forward w hw a b goals⟩⟩
  · intro a b hi _
    obtain ⟨rfl, rfl⟩ := hi rfl
    exact ⟨⟨_, _, by simp [andPortals], by simp [andPortals], and_C_backward w hw goals C.right⟩⟩

/-- Assemble all six OR port macros into the same uniform physical contract. -/
theorem orContract (w : ℕ) (hw : 2 ≤ w) (goals : Finset (Cell (side w) (side w)))
    (C : OrConnections w goals) :
    Contract false (orBoard w goals) (fun s => orBoxes w s.left s.upper s.right) (orPortals w) := by
  constructor
  · intro b c hi _
    cases b with
    | false =>
      have hc := or_both_closed c hi
      subst c
      exact ⟨⟨_, _, by simp [orPortals], by simp [orPortals], or_A_forward w hw false goals C.left⟩⟩
    | true => exact ⟨⟨_, _, by simp [orPortals], by simp [orPortals], or_A_forward_B w hw c goals⟩⟩
  · intro b c _ _
    exact ⟨⟨_, _, by simp [orPortals], by simp [orPortals], or_A_backward w hw b c goals⟩⟩
  · intro a c hi _
    cases a with
    | false =>
      have hc := or_both_closed c hi
      subst c
      exact ⟨⟨_, _, by simp [orPortals], by simp [orPortals], or_B_forward_right w hw false goals C.upper⟩⟩
    | true => exact ⟨⟨_, _, by simp [orPortals], by simp [orPortals], or_B_forward_A w hw c goals⟩⟩
  · intro a c _ _
    exact ⟨⟨_, _, by simp [orPortals], by simp [orPortals], or_B_backward w hw a c goals⟩⟩
  · intro a b _ _
    exact ⟨⟨_, _, by simp [orPortals], by simp [orPortals], or_C_forward w hw a b goals⟩⟩
  · intro a b hi _
    cases a with
    | false =>
      have hb : b = true := (hi rfl).resolve_left (by simp)
      subst b
      exact ⟨⟨_, _, by simp [orPortals], by simp [orPortals], or_C_backward_B w hw goals C.right_B⟩⟩
    | true => exact ⟨⟨_, _, by simp [orPortals], by simp [orPortals], or_C_backward_A w hw b goals (C.right_A b)⟩⟩

end PushPuzzle.PushS.FiniteGateForwardContract
