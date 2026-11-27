/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateAApproaches
public import PushS.FiniteGateToolsFrame
public import PushS.FiniteLaneFrames
public import PushS.FiniteAtomFrames
public import PushS.FiniteMouthFrames
public import PushS.FiniteParallelFrames

/-! The complete protected AND A branch on arbitrary ambient boards using only its actual lanes. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateAAmbient

set_option maxRecDepth 8192

open PushFS FiniteGeometry FiniteGateState FiniteGateTools FiniteGateA
open FiniteGateAStraight FiniteGateAApproaches FiniteGateMacros

variable {W H : ℕ}

attribute [local irreducible] FiniteGeometry.side FiniteTools.side

/-- The four narrow sweeps, three shared tools, and four exposed island detours. -/
structure Frames (w : ℕ) (b c : Bool) (e : GridEmbedding (side w) (side w) W H)
    (B : Board W H) (extra : Finset (Cell W H)) : Prop where
  line (k : Segment) : FiniteWireFrame.Frame (k.sweep w).active e B
    ((k.fixed w b c).map e.cells ∪ extra)
  upper : FiniteWireFrame.Frame (FiniteTools.turnActive w) ((upperEmbedding w).trans e) B
    ((outside w (stage w b c 1) (upperLabel w)).map e.cells ∪ extra)
  flip : FiniteWireFrame.Frame (FiniteTools.flipActive w) ((flipEmbedding w).trans e) B
    ((outside w (stage w b c 3) (flipLabel w)).map e.cells ∪ extra)
  protection : FiniteWireFrame.Frame (FiniteTools.turnActive w) ((protectionEmbedding w).trans e) B
    ((outside w (stage w b c 5) (protectionLabel w)).map e.cells ∪ extra)
  detour (k : Detour) : FiniteWireFrame.Frame
    (FiniteAtomFrames.walkActive (k.start w) (k.finish w)) e B
    ((andMixedBoxes w (stage w b c (match k with
      | .upperAcross | .upperDown => 3 | .lowerAcross | .lowerUp => 4))).map e.cells ∪ extra)

namespace Frames

variable {w : ℕ} {b c : Bool} {e : GridEmbedding (side w) (side w) W H}
    {B : Board W H} {extra : Finset (Cell W H)}

private theorem detour_walk (F : Frames w b c e B extra) (k : Detour) :
    Reachable B (some 1)
      (e.extend extra ⟨k.start w, andMixedBoxes w (stage w b c (match k with
        | .upperAcross | .upperDown => 3 | .lowerAcross | .lowerUp => 4))⟩)
      (e.extend extra ⟨k.finish w, andMixedBoxes w (stage w b c (match k with
        | .upperAcross | .upperDown => 3 | .lowerAcross | .lowerUp => 4))⟩) :=
  FiniteAtomFrames.walk_ambient (k.start w) (k.finish w) e (F.detour k)

private theorem west_upper (F : Frames w b c e B extra) :
    Reachable B (some 1)
      (e.extend extra ⟨(Segment.west.sweep w).hub, andMixedBoxes w (stage w b c 1)⟩)
      (e.extend extra ⟨upperEntry w, andMixedBoxes w (stage w b c 1)⟩) := by
  have hr := upper_walk_ambient w (stage w b c 1) true e F.upper
    (FiniteTools.turn_enter_horizontal w)
  simpa only [upper_source, upper_horizontal, upperEntry] using hr

private theorem upper_line (F : Frames w b c e B extra) :
    Reachable B (some 1)
      (e.extend extra ⟨upperExit w, andMixedBoxes w (stage w b c 2)⟩)
      (e.extend extra ⟨(Segment.upper.sweep w).hub, andMixedBoxes w (stage w b c 2)⟩) := by
  have hr := upper_walk_ambient w (stage w b c 1) false e F.upper
    (FiniteTools.turn_exit_vertical w)
  simpa only [upper_target, upper_vertical, upperExit] using hr

private theorem line_upper_reverse (F : Frames w b c e B extra) :
    Reachable B (some 1)
      (e.extend extra ⟨(Segment.upper.sweep w).hub, andMixedBoxes w (stage w b c 2)⟩)
      (e.extend extra ⟨upperEntry w, andMixedBoxes w (stage w b c 2)⟩) := by
  have hr := upper_walk_ambient w (stage w b c 1) false e F.upper
    (FiniteTools.turn_enter_vertical w)
  simpa only [upper_target, upper_vertical, upperEntry] using hr

private theorem upper_line_reverse (F : Frames w b c e B extra) :
    Reachable B (some 1)
      (e.extend extra ⟨upperReverseExit w, andMixedBoxes w (stage w b c 1)⟩)
      (e.extend extra ⟨(Segment.west.sweep w).hub, andMixedBoxes w (stage w b c 1)⟩) := by
  have hr := upper_walk_ambient w (stage w b c 1) true e F.upper
    (FiniteTools.turn_exit_horizontal w)
  simpa only [upper_source, upper_horizontal, upperReverseExit] using hr

private theorem line_protection (F : Frames w b c e B extra) :
    Reachable B (some 1)
      (e.extend extra ⟨(Segment.lower.sweep w).hub, andMixedBoxes w (stage w b c 5)⟩)
      (e.extend extra ⟨protectionEntry w, andMixedBoxes w (stage w b c 5)⟩) := by
  have hr := protection_walk_ambient w (stage w b c 5) false e F.protection
    (FiniteTools.turn_enter_vertical w)
  simpa only [protection_source, protection_vertical, protectionEntry] using hr

private theorem protection_line_reverse (F : Frames w b c e B extra) :
    Reachable B (some 1)
      (e.extend extra ⟨protectionReverseExit w, andMixedBoxes w (stage w b c 5)⟩)
      (e.extend extra ⟨(Segment.lower.sweep w).hub, andMixedBoxes w (stage w b c 5)⟩) := by
  have hr := protection_walk_ambient w (stage w b c 5) false e F.protection
    (FiniteTools.turn_exit_vertical w)
  simpa only [protection_source, protection_vertical, protectionReverseExit] using hr

private theorem protection_line (F : Frames w b c e B extra) :
    Reachable B (some 1)
      (e.extend extra ⟨protectionExit w, andMixedBoxes w (stage w b c 6)⟩)
      (e.extend extra ⟨(Segment.guard.sweep w).hub, andMixedBoxes w (stage w b c 6)⟩) := by
  have hr := protection_walk_ambient w (stage w b c 5) true e F.protection
    (FiniteTools.turn_exit_horizontal w)
  rw [protection_target, protection_horizontal] at hr
  have hl := Segment.lane_walk_placed w b c false .guard e (F.line .guard)
    (Segment.guard.sweep w).line.leftGap (Segment.guard.sweep w).line.hub
    ((Segment.guard.sweep w).line.leftGap_lane) ((Segment.guard.sweep w).line.hub_lane)
  exact hr.trans hl

private theorem line_protection_reverse (F : Frames w b c e B extra) :
    Reachable B (some 1)
      (e.extend extra ⟨(Segment.guard.sweep w).hub, andMixedBoxes w (stage w b c 6)⟩)
      (e.extend extra ⟨protectionEntry w, andMixedBoxes w (stage w b c 6)⟩) := by
  have hl := Segment.lane_walk_placed w b c false .guard e (F.line .guard)
    (Segment.guard.sweep w).line.hub (Segment.guard.sweep w).line.leftGap
    ((Segment.guard.sweep w).line.hub_lane) ((Segment.guard.sweep w).line.leftGap_lane)
  have hr := protection_walk_ambient w (stage w b c 5) true e F.protection
    (FiniteTools.turn_enter_horizontal w)
  rw [protection_target, protection_horizontal] at hr
  exact hl.trans hr

private theorem flip_line (hw : 2 ≤ w) (F : Frames w b c e B extra) :
    Reachable B (some 1)
      (e.extend extra ⟨flipExit w, andMixedBoxes w (stage w b c 4)⟩)
      (e.extend extra ⟨(Segment.lower.sweep w).hub, andMixedBoxes w (stage w b c 4)⟩) := by
  have hr := flip_walk_ambient w (stage w b c 3) true e F.flip
    (FiniteTools.flip_exit_upper w hw)
  rw [flip_target, flip_upper_exit] at hr
  have hl := Segment.lane_walk_placed w b c false .lower e (F.line .lower)
    (Segment.lower.sweep w).line.leftGap (Segment.lower.sweep w).line.hub
    ((Segment.lower.sweep w).line.leftGap_lane) ((Segment.lower.sweep w).line.hub_lane)
  exact hr.trans hl

private theorem flip_line_reverse (hw : 2 ≤ w) (F : Frames w b c e B extra) :
    Reachable B (some 1)
      (e.extend extra ⟨flipReverseExit w, andMixedBoxes w (stage w b c 3)⟩)
      (e.extend extra ⟨(Segment.upper.sweep w).hub, andMixedBoxes w (stage w b c 3)⟩) := by
  have hr := flip_walk_ambient w (stage w b c 3) false e F.flip
    (FiniteTools.flip_exit_lower w hw)
  rw [flip_source, flip_lower_exit] at hr
  have hl := Segment.lane_walk_placed w b c true .upper e (F.line .upper)
    (Segment.upper.sweep w).line.rightGap (Segment.upper.sweep w).line.hub
    ((Segment.upper.sweep w).line.rightGap_lane) ((Segment.upper.sweep w).line.hub_lane)
  exact hr.trans hl

private theorem line_flip (hw : 2 ≤ w) (F : Frames w b c e B extra) :
    Reachable B (some 1)
      (e.extend extra ⟨(Segment.upper.sweep w).hub, andMixedBoxes w (stage w b c 3)⟩)
      (e.extend extra ⟨flipEntry w, andMixedBoxes w (stage w b c 3)⟩) := by
  have hr := flip_walk_ambient w (stage w b c 3) false e F.flip
    (FiniteTools.flip_enter_forward w hw)
  rw [flip_source] at hr
  exact (F.detour_walk .upperAcross).trans ((F.detour_walk .upperDown).trans hr)

private theorem line_flip_reverse (hw : 2 ≤ w) (F : Frames w b c e B extra) :
    Reachable B (some 1)
      (e.extend extra ⟨(Segment.lower.sweep w).hub, andMixedBoxes w (stage w b c 4)⟩)
      (e.extend extra ⟨flipReverseEntry w, andMixedBoxes w (stage w b c 4)⟩) := by
  have hr := flip_walk_ambient w (stage w b c 3) true e F.flip
    (FiniteTools.flip_enter_backward w hw)
  rw [flip_target] at hr
  exact (F.detour_walk .lowerAcross).trans ((F.detour_walk .lowerUp).trans hr)

end Frames

/-- The final left push uses the finite cavity row and the single cell above its right mouth. -/
def triggerForwardActive (w : ℕ) : Finset (Cell (side w) (side w)) :=
  FiniteMouthFrames.leftActive (point w (w+4) 0).1 (point w 2 0).1
    (point w 0 1).2 (point w 0 0).2

/-- The reverse A trigger uses its three row cells and the adjacent two-cell upper lane. -/
def triggerBackwardActive (w : ℕ) : Finset (Cell (side w) (side w)) :=
  FiniteParallelFrames.active (point w 1 0).1 (point w 1 0).1
    (point w 2 0).1 (point w 3 0).1 (point w 0 1).2 (point w 0 0).2

private theorem trigger_mem (w : ℕ) (b c : Bool) : point w 2 0 ∈ andBoxes w true b c := by
  have he : andCell w true b c .triggerA = point w 2 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]
  rw [← he]
  exact Finset.mem_image.mpr ⟨.triggerA, Finset.mem_univ _, rfl⟩

/-- Finish the completely prepared A branch through the actual right mouth. -/
theorem trigger_forward (w : ℕ) (hw : 2 ≤ w) (b : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (triggerForwardActive w) e B
      (((andBoxes w true b false).erase (point w 2 0)).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w (w+4) 1, andMixedBoxes w (stage w b false 7)⟩)
      (e.extend extra ⟨point w (w+4) 1, andBoxes w true b false⟩) := by
  have hr := FiniteMouthFrames.left_restore_ambient
    (point w (w+4) 0).1 (point w 4 0).1 (point w 3 0).1 (point w 2 0).1
    (point w 0 1).2 (point w 0 0).2
    (by dsimp [Adjacent, point]; unfold origin; omega)
    (by dsimp [Adjacent, point]; omega)
    (by dsimp [Adjacent, point]; omega)
    (by dsimp [point]; omega)
    (andBoxes w true b false) (trigger_mem w b false) e F
  rw [stage_seven_boxes w hw b false]
  exact hr

/-- Open the A trigger from the exposed upper lane, retaining every prepared auxiliary box. -/
theorem trigger_backward (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (triggerBackwardActive w) e B
      (((andBoxes w true b c).erase (point w 2 0)).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 1 1, andBoxes w true b c⟩)
      (e.extend extra ⟨point w 1 1, andMixedBoxes w (stage w b c 7)⟩) := by
  have hr := FiniteParallelFrames.update_ambient
    (point w 1 0).1 (point w 1 0).1 (point w 2 0).1 (point w 3 0).1
    (point w 0 1).2 (point w 0 0).2 .south .east
    (by dsimp [Adjacent, point]; unfold origin; omega)
    (by dsimp [Adjacent, Direction.opposite, point]; unfold origin; omega)
    (by dsimp [Adjacent, point]; omega)
    (by dsimp [Adjacent, point]; omega)
    (andBoxes w true b c) (trigger_mem w b c) e F
  rw [stage_seven_boxes w hw b c]
  exact hr

/-- All A auxiliaries and the final trigger update on the ambient board; only outer-face access remains. -/
theorem and_A_forward (w : ℕ) (hw : 2 ≤ w) (b : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)} (F : Frames w b false e B extra)
    (FT : FiniteWireFrame.Frame (triggerForwardActive w) e B
      (((andBoxes w true b false).erase (point w 2 0)).map e.cells ∪ extra))
    (hfinal : Reachable B (some 1)
      (e.extend extra ⟨(Segment.guard.sweep w).hub, andMixedBoxes w (stage w b false 7)⟩)
      (e.extend extra ⟨point w (w+4) 1, andMixedBoxes w (stage w b false 7)⟩)) :
    Reachable B (some 1)
      (e.extend extra ⟨(Segment.west.sweep w).hub, andBoxes w false b false⟩)
      (e.extend extra ⟨point w (w+4) 1, andBoxes w true b false⟩) := by
  have hW := Segment.forward_placed w b false .west e (F.line .west)
  have hU := upper_backward_ambient w (stage w b false 1) e F.upper
  rw [upper_source, upper_target] at hU
  have hUL := Segment.forward_placed w b false .upper e (F.line .upper)
  have hF := flip_forward_ambient w hw (stage w b false 3) e F.flip
  rw [flip_source, flip_target] at hF
  have hLL := Segment.forward_placed w b false .lower e (F.line .lower)
  have hP := protection_forward_ambient w (stage w b false 5) e F.protection
  rw [protection_source, protection_target] at hP
  have hG := Segment.forward_placed w b false .guard e (F.line .guard)
  have hA := trigger_forward w hw b e FT
  have h1 := (hW.trans F.west_upper).trans hU
  have h2 := ((h1.trans F.upper_line).trans hUL).trans (F.line_flip hw)
  have h3 := ((h2.trans hF).trans (F.flip_line hw)).trans hLL
  have h4 := ((h3.trans F.line_protection).trans hP).trans F.protection_line
  have hr := ((h4.trans hG).trans hfinal).trans hA
  simpa only [Segment.before, stage_zero_boxes] using hr

/-- Reverse the whole protected A branch with all travel supplied by narrow local frames. -/
theorem and_A_backward (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)} (F : Frames w b c e B extra)
    (FT : FiniteWireFrame.Frame (triggerBackwardActive w) e B
      (((andBoxes w true b c).erase (point w 2 0)).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 1 1, andBoxes w true b c⟩)
      (e.extend extra ⟨(Segment.west.sweep w).hub, andBoxes w false b c⟩) := by
  have hA := trigger_backward w hw b c e FT
  have hG := Segment.backward_placed w b c .guard e (F.line .guard)
  have hP := protection_backward_ambient w (stage w b c 5) e F.protection
  rw [protection_source, protection_target] at hP
  have hLL := Segment.backward_placed w b c .lower e (F.line .lower)
  have hF := flip_backward_ambient w hw (stage w b c 3) e F.flip
  rw [flip_source, flip_target] at hF
  have hUL := Segment.backward_placed w b c .upper e (F.line .upper)
  have hU := upper_forward_ambient w (stage w b c 1) e F.upper
  rw [upper_source, upper_target] at hU
  have hW := Segment.backward_placed w b c .west e (F.line .west)
  have hguardHub : (Segment.guard.sweep w).hub = point w 1 1 := rfl
  rw [hguardHub] at hG
  have h1 := ((hA.trans hG).trans F.line_protection_reverse).trans hP
  have h2 := ((h1.trans F.protection_line_reverse).trans hLL).trans (F.line_flip_reverse hw)
  have h3 := ((h2.trans hF).trans (F.flip_line_reverse hw)).trans hUL
  have h4 := ((h3.trans F.line_upper_reverse).trans hU).trans F.upper_line_reverse
  have hr := h4.trans hW
  simpa only [Segment.before, stage_zero_boxes] using hr

end PushPuzzle.PushS.FiniteGateAAmbient
