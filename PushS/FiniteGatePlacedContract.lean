/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateAAmbient
public import PushS.FiniteGateBAmbient
public import PushS.FiniteGateCAmbient
public import PushS.FiniteGateOrAAmbient
public import PushS.FiniteGateAmbientContract

/-! Uniform legal-single-change gate contracts assembled from the actual narrow ambient programs. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGatePlacedContract

open PushFS PushFS.Gadgets FiniteGeometry FiniteGateMacros FiniteGateState
open FiniteGateAStraight FiniteGateVertical FiniteGateOutputs FiniteGateInputs
open FiniteGateBranchSweeps FiniteGateBTemporary FiniteGateForwardContract

variable {W H : ℕ}

attribute [local irreducible] side

/-- All four outer-face transfers required by a placed AND gate, on their exact prepared stocks. -/
structure AndFaces (w : ℕ) (e : GridEmbedding (side w) (side w) W H)
    (B : Board W H) (extra : Finset (Cell W H)) : Prop where
  left : ∀ b, Reachable B (some 1)
    (e.extend extra ⟨(Segment.guard.sweep w).hub,andMixedBoxes w (stage w b false 7)⟩)
    (e.extend extra ⟨point w (w+4) 1,andMixedBoxes w (stage w b false 7)⟩)
  upper_open : Reachable B (some 1)
    (e.extend extra ⟨point w 2 2,andBBoxes w true false true⟩)
    (e.extend extra ⟨point w (w+4) 1,andBBoxes w true false true⟩)
  upper_closed : Reachable B (some 1)
    (e.extend extra ⟨point w 2 1,temporaryBoxes w⟩)
    (e.extend extra ⟨point w (w+4) 1,temporaryBoxes w⟩)
  right : Reachable B (some 1)
    (e.extend extra ⟨point w (w+6) 1,andOutputBoxes w true true false⟩)
    (e.extend extra ⟨point w 3 1,andOutputBoxes w true true false⟩)

/-- All remaining outer-face transfers required by a placed OR gate. -/
structure OrFaces (w : ℕ) (e : GridEmbedding (side w) (side w) W H)
    (B : Board W H) (extra : Finset (Cell W H)) : Prop where
  left : Reachable B (some 1)
    (e.extend extra ⟨point w 1 1,orInputBoxes w false false true⟩)
    (e.extend extra ⟨point w (w+5) 1,orInputBoxes w false false true⟩)
  upper : Reachable B (some 1)
    (e.extend extra ⟨point w 3 2,orBBoxes w false false true⟩)
    (e.extend extra ⟨point w (w+5) 1,orBBoxes w false false true⟩)
  right_A : ∀ b, Reachable B (some 1)
    (e.extend extra ⟨point w (w+7) 1,orOutputBoxes w true b false⟩)
    (e.extend extra ⟨point w 3 1,orOutputBoxes w true b false⟩)
  right_B : Reachable B (some 1)
    (e.extend extra ⟨point w (w+7) 1,orOutputBoxes w false true false⟩)
    (e.extend extra ⟨point w 4 1,orOutputBoxes w false true false⟩)

/-- Narrow concrete working and walking footprints of every placed AND branch. -/
structure AndFrames (w : ℕ) (e : GridEmbedding (side w) (side w) W H)
    (B : Board W H) (extra : Finset (Cell W H)) : Prop where
  auxiliary (b c : Bool) : FiniteGateAAmbient.Frames w b c e B extra
  a_backward (b c : Bool) : FiniteWireFrame.Frame (FiniteGateAAmbient.triggerBackwardActive w) e B
    (((andBoxes w true b c).erase (point w 2 0)).map e.cells ∪ extra)
  a_forward (b : Bool) : FiniteWireFrame.Frame (FiniteGateAAmbient.triggerForwardActive w) e B
    (((andBoxes w true b false).erase (point w 2 0)).map e.cells ∪ extra)
  b_line (a c : Bool) : FiniteWireFrame.Frame ((andBSweep w).active) e B
    ((andBFixed w a c).map e.cells ∪ extra)
  b_backward (a c : Bool) : FiniteWireFrame.Frame (FiniteGateBAmbient.backwardActive w 3 (by omega)) e B
    (((andBoxes w a true c).erase (point w 3 2)).map e.cells ∪ extra)
  b_raise : FiniteWireFrame.Frame (FiniteGateBAmbient.raiseActive w 3 (by omega)) e B
    (((andBoxes w true true false).erase (point w 3 2)).map e.cells ∪ extra)
  b_exit : FiniteWireFrame.Frame (FiniteGateBAmbient.exitActive w 3 (by omega)) e B
    ((andBoxes w true true false).map e.cells ∪ extra)
  b_entry : FiniteWireFrame.Frame (FiniteGateBAmbient.entryActive w (w+4) 3 (by omega) (by omega)) e B
    ((andBBoxes w true false true).map e.cells ∪ extra)
  temp_approach : FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (point w 2 2) (point w 2 0)) e B
    ((andBBoxes w false false true).map e.cells ∪ extra)
  temp_A : FiniteWireFrame.Frame (FiniteAtomFrames.pushActive (point w 2 0) (point w 3 0) (point w 4 0)) e B
    (((andBBoxes w false false true).erase (point w 3 0)).map e.cells ∪ extra)
  temp_B : FiniteWireFrame.Frame (FiniteGateBAmbient.raiseActive w 3 (by omega)) e B
    (((temporaryBoxes w).erase (point w 3 2)).map e.cells ∪ extra)
  temp_exit : FiniteWireFrame.Frame (FiniteGateBAmbient.exitActive w 3 (by omega)) e B
    ((temporaryBoxes w).map e.cells ∪ extra)
  temp_restore : FiniteWireFrame.Frame (FiniteMouthFrames.leftActive (point w (w+4) 0).1 (point w 3 0).1 (point w 0 1).2 (point w 0 0).2) e B
    (((andBoxes w false true false).erase (point w 3 0)).map e.cells ∪ extra)
  c_line (a b : Bool) : FiniteWireFrame.Frame ((andOutputSweep w).active) e B
    ((andOutputFixed w a b).map e.cells ∪ extra)
  c_forward (a b : Bool) : FiniteWireFrame.Frame (FiniteGateCAmbient.forwardActive w 6 (by omega)) e B
    (((andBoxes w a b false).erase (point w (w+5) 0)).map e.cells ∪ extra)
  c_backward : FiniteWireFrame.Frame (FiniteGateCAmbient.backwardActive w 3 6 (by omega) (by omega)) e B
    (((andBoxes w true true false).erase (point w (w+5) 0)).map e.cells ∪ extra)

/-- Narrow concrete working and walking footprints of every placed OR branch. -/
structure OrFrames (w : ℕ) (e : GridEmbedding (side w) (side w) W H)
    (B : Board W H) (extra : Finset (Cell W H)) : Prop where
  a_line (b c : Bool) : FiniteWireFrame.Frame ((orInputSweep w).active) e B
    ((orInputFixed w b c).map e.cells ∪ extra)
  a_backward (b c : Bool) : FiniteWireFrame.Frame (FiniteGateOrAAmbient.backwardActive w) e B
    (((orBoxes w true b c).erase (point w 2 0)).map e.cells ∪ extra)
  a_forward_right : FiniteWireFrame.Frame (FiniteGateOrAAmbient.forwardActive w (w+5) (by omega)) e B
    (((orBoxes w true false false).erase (point w 2 0)).map e.cells ∪ extra)
  a_forward_B (c : Bool) : FiniteWireFrame.Frame (FiniteGateOrAAmbient.forwardActive w 4 (by omega)) e B
    (((orBoxes w true true c).erase (point w 2 0)).map e.cells ∪ extra)
  a_B_connect (c : Bool) : FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (point w 1 1) (point w 4 1)) e B
    ((orInputBoxes w true c true).map e.cells ∪ extra)
  b_line (a c : Bool) : FiniteWireFrame.Frame ((orBSweep w).active) e B
    ((orBFixed w a c).map e.cells ∪ extra)
  b_backward (a c : Bool) : FiniteWireFrame.Frame (FiniteGateBAmbient.backwardActive w 4 (by omega)) e B
    (((orBoxes w a true c).erase (point w 4 2)).map e.cells ∪ extra)
  b_raise (a c : Bool) : FiniteWireFrame.Frame (FiniteGateBAmbient.raiseActive w 4 (by omega)) e B
    (((orBoxes w a true c).erase (point w 4 2)).map e.cells ∪ extra)
  b_exit (a c : Bool) : FiniteWireFrame.Frame (FiniteGateBAmbient.exitActive w 4 (by omega)) e B
    ((orBoxes w a true c).map e.cells ∪ extra)
  b_entry_right : FiniteWireFrame.Frame (FiniteGateBAmbient.entryActive w (w+5) 4 (by omega) (by omega)) e B
    ((orBBoxes w false false true).map e.cells ∪ extra)
  b_entry_A (c : Bool) : FiniteWireFrame.Frame (FiniteGateBAmbient.entryActive w 3 4 (by omega) (by omega)) e B
    ((orBBoxes w true c true).map e.cells ∪ extra)
  b_A_connect (c : Bool) : FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (point w 3 2) (point w 3 1)) e B
    ((orBBoxes w true c true).map e.cells ∪ extra)
  c_line (a b : Bool) : FiniteWireFrame.Frame ((orOutputSweep w).active) e B
    ((orOutputFixed w a b).map e.cells ∪ extra)
  c_forward (a b : Bool) : FiniteWireFrame.Frame (FiniteGateCAmbient.forwardActive w 7 (by omega)) e B
    (((orBoxes w a b false).erase (point w (w+6) 0)).map e.cells ∪ extra)
  c_backward_A (b : Bool) : FiniteWireFrame.Frame (FiniteGateCAmbient.backwardActive w 3 7 (by omega) (by omega)) e B
    (((orBoxes w true b false).erase (point w (w+6) 0)).map e.cells ∪ extra)
  c_backward_B : FiniteWireFrame.Frame (FiniteGateCAmbient.backwardActive w 4 7 (by omega) (by omega)) e B
    (((orBoxes w false true false).erase (point w (w+6) 0)).map e.cells ∪ extra)

private theorem and_left_closed (b c : Bool) (h : Gates.legal true ⟨false,b,c⟩) : c = false := by
  cases c <;> simp [Gates.legal] at h ⊢

private theorem and_upper_closed (a c : Bool) (h : Gates.legal true ⟨a,false,c⟩) : c = false := by
  cases c <;> simp [Gates.legal] at h ⊢

private theorem or_both_closed (c : Bool) (h : Gates.legal false ⟨false,false,c⟩) : c = false := by
  cases c <;> simp [Gates.legal] at h ⊢

/-- Every legal AND signal change is realized on the ambient board by the complete concrete branch programs. -/
theorem andContract (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) (B : Board W H) (extra : Finset (Cell W H))
    (F : AndFrames w e B extra) (C : AndFaces w e B extra) :
    Contract true B (fun s => (andBoxes w s.left s.upper s.right).map e.cells ∪ extra)
      ((andPortals w).map e.cells) := by
  constructor
  · intro b c hi _
    have hc := and_left_closed b c hi
    subst c
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [andPortals]) (by simp [andPortals])
      (FiniteGateAAmbient.and_A_forward w hw b e (F.auxiliary b false) (F.a_forward b) (C.left b))⟩
  · intro b c _ _
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [andPortals]) (by simp [andPortals])
      (FiniteGateAAmbient.and_A_backward w hw b c e (F.auxiliary b c) (F.a_backward b c))⟩
  · intro a c hi _
    have hc := and_upper_closed a c hi
    subst c
    cases a with
    | false =>
      exact ⟨Macro.of_placed_run e extra _ _ (by simp [andPortals]) (by simp [andPortals])
        (FiniteGateBAmbient.and_B_forward_closedA w hw e (F.b_line false false)
          F.temp_approach F.temp_A F.temp_B F.temp_exit F.temp_restore C.upper_closed)⟩
    | true =>
      exact ⟨Macro.of_placed_run e extra _ _ (by simp [andPortals]) (by simp [andPortals])
        (FiniteGateBAmbient.and_B_forward w hw true false (w+4) (by omega) e
          (F.b_line true false) F.b_entry F.b_raise F.b_exit C.upper_open)⟩
  · intro a c _ _
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [andPortals]) (by simp [andPortals])
      (FiniteGateBAmbient.and_B_backward w hw a c e (F.b_backward a c) (F.b_line a c))⟩
  · intro a b _ _
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [andPortals]) (by simp [andPortals])
      (FiniteGateCAmbient.and_C_forward w hw a b e (F.c_forward a b) (F.c_line a b))⟩
  · intro a b hi _
    obtain ⟨ha,hb⟩ := hi rfl
    change a = true at ha
    change b = true at hb
    subst a
    subst b
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [andPortals]) (by simp [andPortals])
      (FiniteGateCAmbient.and_C_backward w hw true true 3 (by omega) (by omega) e
        (F.c_line true true) F.c_backward C.right)⟩

/-- Every legal OR signal change is realized on the ambient board by the complete concrete branch programs. -/
theorem orContract (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) (B : Board W H) (extra : Finset (Cell W H))
    (F : OrFrames w e B extra) (C : OrFaces w e B extra) :
    Contract false B (fun s => (orBoxes w s.left s.upper s.right).map e.cells ∪ extra)
      ((orPortals w).map e.cells) := by
  constructor
  · intro b c hi _
    cases b with
    | false =>
      have hc := or_both_closed c hi
      subst c
      exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
        (FiniteGateOrAAmbient.or_A_forward w hw false false (w+5) (by omega) (by omega) e
          (F.a_line false false) F.a_forward_right C.left)⟩
    | true =>
      exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
        (FiniteGateOrAAmbient.or_A_forward_B w hw c e (F.a_line true c)
          (F.a_forward_B c) (F.a_B_connect c))⟩
  · intro b c _ _
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
      (FiniteGateOrAAmbient.or_A_backward w hw b c e (F.a_backward b c) (F.a_line b c))⟩
  · intro a c hi _
    cases a with
    | false =>
      have hc := or_both_closed c hi
      subst c
      exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
        (FiniteGateBAmbient.or_B_forward w hw false false (w+5) (by omega) e
          (F.b_line false false) F.b_entry_right (F.b_raise false false)
          (F.b_exit false false) C.upper)⟩
    | true =>
      exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
        (FiniteGateBAmbient.or_B_forward w hw true c 3 (by omega) e
          (F.b_line true c) (F.b_entry_A c) (F.b_raise true c) (F.b_exit true c)
          (FiniteAtomFrames.walk_ambient _ _ e (F.b_A_connect c)))⟩
  · intro a c _ _
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
      (FiniteGateBAmbient.or_B_backward w hw a c e (F.b_backward a c) (F.b_line a c))⟩
  · intro a b _ _
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
      (FiniteGateCAmbient.or_C_forward w hw a b e (F.c_forward a b) (F.c_line a b))⟩
  · intro a b hi _
    cases a with
    | false =>
      have hb : b = true := (hi rfl).resolve_left (by simp)
      subst b
      exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
        (FiniteGateCAmbient.or_C_backward w hw false true 4 (by omega) (by omega) e
          (F.c_line false true) F.c_backward_B C.right_B)⟩
    | true =>
      exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
        (FiniteGateCAmbient.or_C_backward w hw true b 3 (by omega) (by omega) e
          (F.c_line true b) (F.c_backward_A b) (C.right_A b))⟩

end PushPuzzle.PushS.FiniteGatePlacedContract
