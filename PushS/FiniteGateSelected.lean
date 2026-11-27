/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateCanonicalAccess
public import PushS.FiniteGateNormalSeparation

/-! Select exactly one prepared physical branch from an actual legal single-bit gate update. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateSelected

open PushFS PushFS.Gadgets FiniteGeometry FiniteGateMacros FiniteGateState
open FiniteGateAStraight FiniteGateVertical FiniteGateOutputs FiniteGateInputs
open FiniteGateBranchSweeps FiniteGateBTemporary FiniteGateForwardContract
open FiniteGateCanonicalAccess FiniteGateFaceBridge FiniteGateFaceGeometry
open FiniteGateNormalSeparation

variable {W H : ℕ}

attribute [local irreducible] FiniteGeometry.side

/-- Precisely the physical preparation of one selected branch, indexed by its actual endpoint signals. -/
inductive AndStep (w : ℕ) (e : GridEmbedding (side w) (side w) W H)
    (B : Board W H) (extra : Finset (Cell W H)) : Gates.Signals → Gates.Signals → Prop
  | left_on (b : Bool)
    (F : FiniteGateAAmbient.Frames w b false e B extra)
    (FT : FiniteWireFrame.Frame (FiniteGateAAmbient.triggerForwardActive w) e B
      (((andBoxes w true b false).erase (point w 2 0)).map e.cells ∪ extra))
    (hface : Reachable B (some 1)
      (e.extend extra ⟨(Segment.guard.sweep w).hub,andMixedBoxes w (stage w b false 7)⟩) (e.extend extra ⟨point w (w+4) 1,andMixedBoxes w (stage w b false 7)⟩))
    : AndStep w e B extra ⟨false,b,false⟩ ⟨true,b,false⟩
  | left_off (b c : Bool)
    (F : FiniteGateAAmbient.Frames w b c e B extra)
    (FT : FiniteWireFrame.Frame (FiniteGateAAmbient.triggerBackwardActive w) e B
      (((andBoxes w true b c).erase (point w 2 0)).map e.cells ∪ extra))
    : AndStep w e B extra ⟨true,b,c⟩ ⟨false,b,c⟩
  | upper_on_open
    (FL : FiniteWireFrame.Frame ((andBSweep w).active) e B
      ((andBFixed w true false).map e.cells ∪ extra))
    (FA : FiniteWireFrame.Frame (FiniteGateBAmbient.entryActive w (w+4) 3 (by omega) (by omega)) e B
      ((andBBoxes w true false true).map e.cells ∪ extra))
    (FP : FiniteWireFrame.Frame (FiniteGateBAmbient.raiseActive w 3 (by omega)) e B
      (((andBoxes w true true false).erase (point w 3 2)).map e.cells ∪ extra))
    (FE : FiniteWireFrame.Frame (FiniteGateBAmbient.exitActive w 3 (by omega)) e B
      ((andBoxes w true true false).map e.cells ∪ extra))
    (hface : Reachable B (some 1)
      (e.extend extra ⟨point w 2 2,andBBoxes w true false true⟩) (e.extend extra ⟨point w (w+4) 1,andBBoxes w true false true⟩))
    : AndStep w e B extra ⟨true,false,false⟩ ⟨true,true,false⟩
  | upper_on_closed
    (FL : FiniteWireFrame.Frame ((andBSweep w).active) e B
      ((andBFixed w false false).map e.cells ∪ extra))
    (FA : FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (point w 2 2) (point w 2 0)) e B
      ((andBBoxes w false false true).map e.cells ∪ extra))
    (FP : FiniteWireFrame.Frame (FiniteAtomFrames.pushActive (point w 2 0) (point w 3 0) (point w 4 0)) e B
      (((andBBoxes w false false true).erase (point w 3 0)).map e.cells ∪ extra))
    (FB : FiniteWireFrame.Frame (FiniteGateBAmbient.raiseActive w 3 (by omega)) e B
      (((temporaryBoxes w).erase (point w 3 2)).map e.cells ∪ extra))
    (FE : FiniteWireFrame.Frame (FiniteGateBAmbient.exitActive w 3 (by omega)) e B
      ((temporaryBoxes w).map e.cells ∪ extra))
    (FR : FiniteWireFrame.Frame (FiniteMouthFrames.leftActive (point w (w+4) 0).1 (point w 3 0).1 (point w 0 1).2 (point w 0 0).2) e B
      (((andBoxes w false true false).erase (point w 3 0)).map e.cells ∪ extra))
    (hface : Reachable B (some 1)
      (e.extend extra ⟨point w 2 1,temporaryBoxes w⟩) (e.extend extra ⟨point w (w+4) 1,temporaryBoxes w⟩))
    : AndStep w e B extra ⟨false,false,false⟩ ⟨false,true,false⟩
  | upper_off (a c : Bool)
    (FT : FiniteWireFrame.Frame (FiniteGateBAmbient.backwardActive w 3 (by omega)) e B
      (((andBoxes w a true c).erase (point w 3 2)).map e.cells ∪ extra))
    (FL : FiniteWireFrame.Frame ((andBSweep w).active) e B
      ((andBFixed w a c).map e.cells ∪ extra))
    : AndStep w e B extra ⟨a,true,c⟩ ⟨a,false,c⟩
  | right_on (a b : Bool)
    (FF : FiniteWireFrame.Frame (FiniteGateCAmbient.forwardActive w 6 (by omega)) e B
      (((andBoxes w a b false).erase (point w (w+5) 0)).map e.cells ∪ extra))
    (FL : FiniteWireFrame.Frame ((andOutputSweep w).active) e B
      ((andOutputFixed w a b).map e.cells ∪ extra))
    : AndStep w e B extra ⟨a,b,false⟩ ⟨a,b,true⟩
  | right_off
    (FL : FiniteWireFrame.Frame ((andOutputSweep w).active) e B
      ((andOutputFixed w true true).map e.cells ∪ extra))
    (FR : FiniteWireFrame.Frame (FiniteGateCAmbient.backwardActive w 3 6 (by omega) (by omega)) e B
      (((andBoxes w true true false).erase (point w (w+5) 0)).map e.cells ∪ extra))
    (hface : Reachable B (some 1)
      (e.extend extra ⟨point w (w+6) 1,andOutputBoxes w true true false⟩) (e.extend extra ⟨point w 3 1,andOutputBoxes w true true false⟩))
    : AndStep w e B extra ⟨true,true,true⟩ ⟨true,true,false⟩

/-- The selected preparation yields the complete actual single-box macro for exactly that change. -/
private theorem AndStep.macro (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {extra : Finset (Cell W H)}
    {i f : Gates.Signals} (S : AndStep w e B extra i f) :
    Nonempty (Macro B ((andBoxes w i.left i.upper i.right).map e.cells ∪ extra)
      ((andBoxes w f.left f.upper f.right).map e.cells ∪ extra)
      ((andPortals w).map e.cells)) := by
  cases S with
  | left_on b F FT hface =>
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [andPortals]) (by simp [andPortals])
      (FiniteGateAAmbient.and_A_forward w hw b e F FT hface)⟩
  | left_off b c F FT =>
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [andPortals]) (by simp [andPortals])
      (FiniteGateAAmbient.and_A_backward w hw b c e F FT)⟩
  | upper_on_open FL FA FP FE hface =>
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [andPortals]) (by simp [andPortals])
      (FiniteGateBAmbient.and_B_forward w hw true false (w+4) (by omega) e FL FA FP FE hface)⟩
  | upper_on_closed FL FA FP FB FE FR hface =>
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [andPortals]) (by simp [andPortals])
      (FiniteGateBAmbient.and_B_forward_closedA w hw e FL FA FP FB FE FR hface)⟩
  | upper_off a c FT FL =>
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [andPortals]) (by simp [andPortals])
      (FiniteGateBAmbient.and_B_backward w hw a c e FT FL)⟩
  | right_on a b FF FL =>
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [andPortals]) (by simp [andPortals])
      (FiniteGateCAmbient.and_C_forward w hw a b e FF FL)⟩
  | right_off FL FR hface =>
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [andPortals]) (by simp [andPortals])
      (FiniteGateCAmbient.and_C_backward w hw true true 3 (by omega) (by omega) e FL FR hface)⟩

/-- Precisely the physical preparation of one selected branch, indexed by its actual endpoint signals. -/
inductive OrStep (w : ℕ) (e : GridEmbedding (side w) (side w) W H)
    (B : Board W H) (extra : Finset (Cell W H)) : Gates.Signals → Gates.Signals → Prop
  | left_on_closed
    (FL : FiniteWireFrame.Frame ((orInputSweep w).active) e B
      ((orInputFixed w false false).map e.cells ∪ extra))
    (FT : FiniteWireFrame.Frame (FiniteGateOrAAmbient.forwardActive w (w+5) (by omega)) e B
      (((orBoxes w true false false).erase (point w 2 0)).map e.cells ∪ extra))
    (hface : Reachable B (some 1)
      (e.extend extra ⟨point w 1 1,orInputBoxes w false false true⟩) (e.extend extra ⟨point w (w+5) 1,orInputBoxes w false false true⟩))
    : OrStep w e B extra ⟨false,false,false⟩ ⟨true,false,false⟩
  | left_on_open (c : Bool)
    (FL : FiniteWireFrame.Frame ((orInputSweep w).active) e B
      ((orInputFixed w true c).map e.cells ∪ extra))
    (FT : FiniteWireFrame.Frame (FiniteGateOrAAmbient.forwardActive w 4 (by omega)) e B
      (((orBoxes w true true c).erase (point w 2 0)).map e.cells ∪ extra))
    (FW : FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (point w 1 1) (point w 4 1)) e B
      ((orInputBoxes w true c true).map e.cells ∪ extra))
    : OrStep w e B extra ⟨false,true,c⟩ ⟨true,true,c⟩
  | left_off (b c : Bool)
    (FT : FiniteWireFrame.Frame (FiniteGateOrAAmbient.backwardActive w) e B
      (((orBoxes w true b c).erase (point w 2 0)).map e.cells ∪ extra))
    (FL : FiniteWireFrame.Frame ((orInputSweep w).active) e B
      ((orInputFixed w b c).map e.cells ∪ extra))
    : OrStep w e B extra ⟨true,b,c⟩ ⟨false,b,c⟩
  | upper_on_closed
    (FL : FiniteWireFrame.Frame ((orBSweep w).active) e B
      ((orBFixed w false false).map e.cells ∪ extra))
    (FA : FiniteWireFrame.Frame (FiniteGateBAmbient.entryActive w (w+5) 4 (by omega) (by omega)) e B
      ((orBBoxes w false false true).map e.cells ∪ extra))
    (FP : FiniteWireFrame.Frame (FiniteGateBAmbient.raiseActive w 4 (by omega)) e B
      (((orBoxes w false true false).erase (point w 4 2)).map e.cells ∪ extra))
    (FE : FiniteWireFrame.Frame (FiniteGateBAmbient.exitActive w 4 (by omega)) e B
      ((orBoxes w false true false).map e.cells ∪ extra))
    (hface : Reachable B (some 1)
      (e.extend extra ⟨point w 3 2,orBBoxes w false false true⟩) (e.extend extra ⟨point w (w+5) 1,orBBoxes w false false true⟩))
    : OrStep w e B extra ⟨false,false,false⟩ ⟨false,true,false⟩
  | upper_on_open (c : Bool)
    (FL : FiniteWireFrame.Frame ((orBSweep w).active) e B
      ((orBFixed w true c).map e.cells ∪ extra))
    (FA : FiniteWireFrame.Frame (FiniteGateBAmbient.entryActive w 3 4 (by omega) (by omega)) e B
      ((orBBoxes w true c true).map e.cells ∪ extra))
    (FP : FiniteWireFrame.Frame (FiniteGateBAmbient.raiseActive w 4 (by omega)) e B
      (((orBoxes w true true c).erase (point w 4 2)).map e.cells ∪ extra))
    (FE : FiniteWireFrame.Frame (FiniteGateBAmbient.exitActive w 4 (by omega)) e B
      ((orBoxes w true true c).map e.cells ∪ extra))
    (FW : FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (point w 3 2) (point w 3 1)) e B
      ((orBBoxes w true c true).map e.cells ∪ extra))
    : OrStep w e B extra ⟨true,false,c⟩ ⟨true,true,c⟩
  | upper_off (a c : Bool)
    (FT : FiniteWireFrame.Frame (FiniteGateBAmbient.backwardActive w 4 (by omega)) e B
      (((orBoxes w a true c).erase (point w 4 2)).map e.cells ∪ extra))
    (FL : FiniteWireFrame.Frame ((orBSweep w).active) e B
      ((orBFixed w a c).map e.cells ∪ extra))
    : OrStep w e B extra ⟨a,true,c⟩ ⟨a,false,c⟩
  | right_on (a b : Bool)
    (FF : FiniteWireFrame.Frame (FiniteGateCAmbient.forwardActive w 7 (by omega)) e B
      (((orBoxes w a b false).erase (point w (w+6) 0)).map e.cells ∪ extra))
    (FL : FiniteWireFrame.Frame ((orOutputSweep w).active) e B
      ((orOutputFixed w a b).map e.cells ∪ extra))
    : OrStep w e B extra ⟨a,b,false⟩ ⟨a,b,true⟩
  | right_off_A (b : Bool)
    (FL : FiniteWireFrame.Frame ((orOutputSweep w).active) e B
      ((orOutputFixed w true b).map e.cells ∪ extra))
    (FR : FiniteWireFrame.Frame (FiniteGateCAmbient.backwardActive w 3 7 (by omega) (by omega)) e B
      (((orBoxes w true b false).erase (point w (w+6) 0)).map e.cells ∪ extra))
    (hface : Reachable B (some 1)
      (e.extend extra ⟨point w (w+7) 1,orOutputBoxes w true b false⟩) (e.extend extra ⟨point w 3 1,orOutputBoxes w true b false⟩))
    : OrStep w e B extra ⟨true,b,true⟩ ⟨true,b,false⟩
  | right_off_B
    (FL : FiniteWireFrame.Frame ((orOutputSweep w).active) e B
      ((orOutputFixed w false true).map e.cells ∪ extra))
    (FR : FiniteWireFrame.Frame (FiniteGateCAmbient.backwardActive w 4 7 (by omega) (by omega)) e B
      (((orBoxes w false true false).erase (point w (w+6) 0)).map e.cells ∪ extra))
    (hface : Reachable B (some 1)
      (e.extend extra ⟨point w (w+7) 1,orOutputBoxes w false true false⟩) (e.extend extra ⟨point w 4 1,orOutputBoxes w false true false⟩))
    : OrStep w e B extra ⟨false,true,true⟩ ⟨false,true,false⟩

/-- The selected preparation yields the complete actual single-box macro for exactly that change. -/
private theorem OrStep.macro (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {extra : Finset (Cell W H)}
    {i f : Gates.Signals} (S : OrStep w e B extra i f) :
    Nonempty (Macro B ((orBoxes w i.left i.upper i.right).map e.cells ∪ extra)
      ((orBoxes w f.left f.upper f.right).map e.cells ∪ extra)
      ((orPortals w).map e.cells)) := by
  cases S with
  | left_on_closed FL FT hface =>
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
      (FiniteGateOrAAmbient.or_A_forward w hw false false (w+5) (by omega) (by omega) e FL FT hface)⟩
  | left_on_open c FL FT FW =>
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
      (FiniteGateOrAAmbient.or_A_forward_B w hw c e FL FT FW)⟩
  | left_off b c FT FL =>
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
      (FiniteGateOrAAmbient.or_A_backward w hw b c e FT FL)⟩
  | upper_on_closed FL FA FP FE hface =>
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
      (FiniteGateBAmbient.or_B_forward w hw false false (w+5) (by omega) e FL FA FP FE hface)⟩
  | upper_on_open c FL FA FP FE FW =>
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
      (FiniteGateBAmbient.or_B_forward w hw true c 3 (by omega) e FL FA FP FE (FiniteAtomFrames.walk_ambient _ _ e FW))⟩
  | upper_off a c FT FL =>
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
      (FiniteGateBAmbient.or_B_backward w hw a c e FT FL)⟩
  | right_on a b FF FL =>
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
      (FiniteGateCAmbient.or_C_forward w hw a b e FF FL)⟩
  | right_off_A b FL FR hface =>
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
      (FiniteGateCAmbient.or_C_backward w hw true b 3 (by omega) (by omega) e FL FR hface)⟩
  | right_off_B FL FR hface =>
    exact ⟨Macro.of_placed_run e extra _ _ (by simp [orPortals]) (by simp [orPortals])
      (FiniteGateCAmbient.or_C_backward w hw false true 4 (by omega) (by omega) e FL FR hface)⟩

private theorem extra_avoid {N M : ℕ} {active : Finset (Cell N M)}
    {e : GridEmbedding N M W H} {B : Board W H} {rest extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame active e B (rest ∪ extra)) (p : Cell N M) (hp : p ∈ active) :
    e.cells p ∉ extra := fun hm => F.fixed_avoids p hp (Finset.mem_union_right _ hm)

private theorem probe_ne {N M : ℕ} (e : GridEmbedding N M W H) (extra : Finset (Cell W H))
    (p : Cell N M) (initial final : Finset (Cell N M)) (a b : Bool)
    (hi : p ∈ initial ↔ a = true) (hf : p ∈ final ↔ b = true) (hne : a ≠ b)
    (hp : e.cells p ∉ extra) : initial.map e.cells ∪ extra ≠ final.map e.cells ∪ extra := by
  intro he
  have hm (stock : Finset (Cell N M)) : e.cells p ∈ stock.map e.cells ∪ extra ↔ p ∈ stock := by
    constructor
    · intro hh
      rcases Finset.mem_union.mp hh with hh | hh
      · obtain ⟨q,hq,hq'⟩ := Finset.mem_map.mp hh
        exact e.cells.injective hq' ▸ hq
      · exact False.elim (hp hh)
    · intro hh
      exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨p,hh,rfl⟩)
  have hh : a = true ↔ b = true := by rw [← hi,← hf,← hm initial,← hm final,he]
  cases a <;> cases b <;> simp_all

private theorem and_ne_a (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {active : Finset (Cell (side w) (side w))} {rest extra : Finset (Cell W H)}
    {i f : Gates.Signals} (F : FiniteWireFrame.Frame active e B (rest ∪ extra))
    (hp : point w 2 0 ∈ active) (hne : i.left ≠ f.left) :
    (andBoxes w i.left i.upper i.right).map e.cells ∪ extra ≠
      (andBoxes w f.left f.upper f.right).map e.cells ∪ extra :=
  probe_ne e extra (point w 2 0) _ _ i.left f.left
    (and_probe_a w hw i.left i.upper i.right) (and_probe_a w hw f.left f.upper f.right)
    hne (extra_avoid F _ hp)

private theorem and_ne_b (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {active : Finset (Cell (side w) (side w))} {rest extra : Finset (Cell W H)}
    {i f : Gates.Signals} (F : FiniteWireFrame.Frame active e B (rest ∪ extra))
    (hp : point w 3 2 ∈ active) (hne : i.upper ≠ f.upper) :
    (andBoxes w i.left i.upper i.right).map e.cells ∪ extra ≠
      (andBoxes w f.left f.upper f.right).map e.cells ∪ extra :=
  probe_ne e extra (point w 3 2) _ _ i.upper f.upper
    (and_probe_b w hw i.left i.upper i.right) (and_probe_b w hw f.left f.upper f.right)
    hne (extra_avoid F _ hp)

private theorem and_ne_c (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {active : Finset (Cell (side w) (side w))} {rest extra : Finset (Cell W H)}
    {i f : Gates.Signals} (F : FiniteWireFrame.Frame active e B (rest ∪ extra))
    (hp : point w (w+4) 0 ∈ active) (hne : i.right ≠ f.right) :
    (andBoxes w i.left i.upper i.right).map e.cells ∪ extra ≠
      (andBoxes w f.left f.upper f.right).map e.cells ∪ extra :=
  probe_ne e extra (point w (w+4) 0) _ _ i.right f.right
    (and_probe_c w hw i.left i.upper i.right) (and_probe_c w hw f.left f.upper f.right)
    hne (extra_avoid F _ hp)

private theorem or_ne_a (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {active : Finset (Cell (side w) (side w))} {rest extra : Finset (Cell W H)}
    {i f : Gates.Signals} (F : FiniteWireFrame.Frame active e B (rest ∪ extra))
    (hp : point w 2 0 ∈ active) (hne : i.left ≠ f.left) :
    (orBoxes w i.left i.upper i.right).map e.cells ∪ extra ≠
      (orBoxes w f.left f.upper f.right).map e.cells ∪ extra :=
  probe_ne e extra (point w 2 0) _ _ i.left f.left
    (or_probe_a w hw i.left i.upper i.right) (or_probe_a w hw f.left f.upper f.right)
    hne (extra_avoid F _ hp)

private theorem or_ne_b (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {active : Finset (Cell (side w) (side w))} {rest extra : Finset (Cell W H)}
    {i f : Gates.Signals} (F : FiniteWireFrame.Frame active e B (rest ∪ extra))
    (hp : point w 4 2 ∈ active) (hne : i.upper ≠ f.upper) :
    (orBoxes w i.left i.upper i.right).map e.cells ∪ extra ≠
      (orBoxes w f.left f.upper f.right).map e.cells ∪ extra :=
  probe_ne e extra (point w 4 2) _ _ i.upper f.upper
    (or_probe_b w hw i.left i.upper i.right) (or_probe_b w hw f.left f.upper f.right)
    hne (extra_avoid F _ hp)

private theorem or_ne_c (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {active : Finset (Cell (side w) (side w))} {rest extra : Finset (Cell W H)}
    {i f : Gates.Signals} (F : FiniteWireFrame.Frame active e B (rest ∪ extra))
    (hp : point w (w+5) 0 ∈ active) (hne : i.right ≠ f.right) :
    (orBoxes w i.left i.upper i.right).map e.cells ∪ extra ≠
      (orBoxes w f.left f.upper f.right).map e.cells ∪ extra :=
  probe_ne e extra (point w (w+5) 0) _ _ i.right f.right
    (or_probe_c w hw i.left i.upper i.right) (or_probe_c w hw f.left f.upper f.right)
    hne (extra_avoid F _ hp)

/-- The selected trigger frame itself distinguishes the two complete inventories. -/
private theorem AndStep.normal_ne (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {extra : Finset (Cell W H)}
    {i f : Gates.Signals} (S : AndStep w e B extra i f) :
    (andBoxes w i.left i.upper i.right).map e.cells ∪ extra ≠
      (andBoxes w f.left f.upper f.right).map e.cells ∪ extra := by
  cases S with
  | left_on b F FT hface =>
    apply and_ne_a w hw e FT ?_ (by simp)
    simp [FiniteGateAAmbient.triggerForwardActive,FiniteMouthFrames.leftActive,point]
  | left_off b c F FT =>
    apply and_ne_a w hw e FT ?_ (by simp)
    simp [FiniteGateAAmbient.triggerBackwardActive,FiniteParallelFrames.active,point]
  | upper_on_open FL FA FP FE hface =>
    apply and_ne_b w hw e FP ?_ (by simp)
    simp [FiniteGateBAmbient.raiseActive,FiniteAtomFrames.pushActive]
  | upper_on_closed FL FA FP FB FE FR hface =>
    apply and_ne_b w hw e FB ?_ (by simp)
    simp [FiniteGateBAmbient.raiseActive,FiniteAtomFrames.pushActive]
  | upper_off a c FT FL =>
    apply and_ne_b w hw e FT ?_ (by simp)
    apply Finset.mem_map.mpr
    refine ⟨((point w 0 2).2,(point w 3 0).1),?_,rfl⟩
    dsimp [FiniteGateBAmbient.downLocalActive,FiniteParallelFrames.active]
    apply Finset.mem_union_left
    simp
  | right_on a b FF FL =>
    apply and_ne_c w hw e FF ?_ (by simp)
    simp [FiniteGateCAmbient.forwardActive,FiniteParallelFrames.active,point]
  | right_off FL FR hface =>
    apply and_ne_c w hw e FR ?_ (by simp)
    simp [FiniteGateCAmbient.backwardActive,FiniteMouthFrames.rightActive,point]

/-- The selected trigger frame itself distinguishes the two complete inventories. -/
private theorem OrStep.normal_ne (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {extra : Finset (Cell W H)}
    {i f : Gates.Signals} (S : OrStep w e B extra i f) :
    (orBoxes w i.left i.upper i.right).map e.cells ∪ extra ≠
      (orBoxes w f.left f.upper f.right).map e.cells ∪ extra := by
  cases S with
  | left_on_closed FL FT hface =>
    apply or_ne_a w hw e FT ?_ (by simp)
    simp [FiniteGateOrAAmbient.forwardActive,FiniteMouthFrames.leftActive,point]
  | left_on_open c FL FT FW =>
    apply or_ne_a w hw e FT ?_ (by simp)
    simp [FiniteGateOrAAmbient.forwardActive,FiniteMouthFrames.leftActive,point]
  | left_off b c FT FL =>
    apply or_ne_a w hw e FT ?_ (by simp)
    simp [FiniteGateOrAAmbient.backwardActive,FiniteParallelFrames.active,point]
  | upper_on_closed FL FA FP FE hface =>
    apply or_ne_b w hw e FP ?_ (by simp)
    simp [FiniteGateBAmbient.raiseActive,FiniteAtomFrames.pushActive]
  | upper_on_open c FL FA FP FE FW =>
    apply or_ne_b w hw e FP ?_ (by simp)
    simp [FiniteGateBAmbient.raiseActive,FiniteAtomFrames.pushActive]
  | upper_off a c FT FL =>
    apply or_ne_b w hw e FT ?_ (by simp)
    apply Finset.mem_map.mpr
    refine ⟨((point w 0 2).2,(point w 4 0).1),?_,rfl⟩
    dsimp [FiniteGateBAmbient.downLocalActive,FiniteParallelFrames.active]
    apply Finset.mem_union_left
    simp
  | right_on a b FF FL =>
    apply or_ne_c w hw e FF ?_ (by simp)
    simp [FiniteGateCAmbient.forwardActive,FiniteParallelFrames.active,point]
  | right_off_A b FL FR hface =>
    apply or_ne_c w hw e FR ?_ (by simp)
    simp [FiniteGateCAmbient.backwardActive,FiniteMouthFrames.rightActive,point]
  | right_off_B FL FR hface =>
    apply or_ne_c w hw e FR ?_ (by simp)
    simp [FiniteGateCAmbient.backwardActive,FiniteMouthFrames.rightActive,point]

/-- Execute only the prepared arm, using actual canonical access at the two endpoint inventories. -/
theorem AndStep.canonical_run (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {extra : Finset (Cell W H)}
    {i f : Gates.Signals} (S : AndStep w e B extra i f)
    (Ai : AndAccess w e B ((andBoxes w i.left i.upper i.right).map e.cells ∪ extra))
    (Af : AndAccess w e B ((andBoxes w f.left f.upper f.right).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨dock w true true,andBoxes w i.left i.upper i.right⟩)
      (e.extend extra ⟨dock w true true,andBoxes w f.left f.upper f.right⟩) := by
  obtain ⟨M⟩ := S.macro w hw e
  have hfree := M.interface_free (S.normal_ne w hw e)
  have hi : Reachable B (some 1)
      ⟨e.cells (dock w true true),(andBoxes w i.left i.upper i.right).map e.cells ∪ extra⟩
      ⟨M.entry,(andBoxes w i.left i.upper i.right).map e.cells ∪ extra⟩ := by
    obtain ⟨q,hq,he⟩ := Finset.mem_map.mp M.entry_mem
    simpa only [he] using (Ai.access w hw e q hq (by simpa only [he] using hfree.1)).1
  have hf : Reachable B (some 1)
      ⟨M.exit,(andBoxes w f.left f.upper f.right).map e.cells ∪ extra⟩
      ⟨e.cells (dock w true true),(andBoxes w f.left f.upper f.right).map e.cells ∪ extra⟩ := by
    obtain ⟨q,hq,he⟩ := Finset.mem_map.mp M.exit_mem
    simpa only [he] using (Af.access w hw e q hq (by simpa only [he] using hfree.2)).2
  exact hi.trans (M.run.trans hf)

/-- Execute only the prepared arm, using actual canonical access at the two endpoint inventories. -/
theorem OrStep.canonical_run (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {extra : Finset (Cell W H)}
    {i f : Gates.Signals} (S : OrStep w e B extra i f)
    (Ai : Access w false e B ((orBoxes w i.left i.upper i.right).map e.cells ∪ extra))
    (Af : Access w false e B ((orBoxes w f.left f.upper f.right).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨dock w false true,orBoxes w i.left i.upper i.right⟩)
      (e.extend extra ⟨dock w false true,orBoxes w f.left f.upper f.right⟩) := by
  obtain ⟨M⟩ := S.macro w hw e
  have hfree := M.interface_free (S.normal_ne w hw e)
  have hi : Reachable B (some 1)
      ⟨e.cells (dock w false true),(orBoxes w i.left i.upper i.right).map e.cells ∪ extra⟩
      ⟨M.entry,(orBoxes w i.left i.upper i.right).map e.cells ∪ extra⟩ := by
    obtain ⟨q,hq,he⟩ := Finset.mem_map.mp M.entry_mem
    simpa only [he] using (or_access w hw e Ai q hq (by simpa only [he] using hfree.1)).1
  have hf : Reachable B (some 1)
      ⟨M.exit,(orBoxes w f.left f.upper f.right).map e.cells ∪ extra⟩
      ⟨e.cells (dock w false true),(orBoxes w f.left f.upper f.right).map e.cells ∪ extra⟩ := by
    obtain ⟨q,hq,he⟩ := Finset.mem_map.mp M.exit_mem
    simpa only [he] using (or_access w hw e Af q hq (by simpa only [he] using hfree.2)).2
  exact hi.trans (M.run.trans hf)

end PushPuzzle.PushS.FiniteGateSelected
