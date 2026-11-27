/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateAStraight
public import PushS.FiniteSquareLineFrame

/-! Narrow active-footprint replay of the AND A-branch straight stages. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateAStraight.Segment

open PushFS FiniteGeometry FiniteGateCore FiniteGateState FiniteSquareLine

variable {W H : ℕ}

private theorem extend_endpoint (w : ℕ) (b c q : Bool) (k : Segment)
    (e : GridEmbedding (side w) (side w) W H) (outside : Finset (Cell W H)) :
    e.extend ((k.fixed w b c).map e.cells ∪ outside)
      ⟨(k.sweep w).hub, Finset.univ.image ((k.sweep w).position (if q then k.count w else 0))⟩ =
      e.extend outside ⟨(k.sweep w).hub, andMixedBoxes w (stage w b c (k.endpoint q))⟩ := by
  apply State.ext
  · rfl
  · rw [← k.boxes_endpoint w b c q]
    simp only [GridEmbedding.extend, Sweep.boxes, Finset.map_union]
    ac_rfl

/-- Place a full forward straight stage while retaining all other local and global boxes. -/
theorem forward_placed (w : ℕ) (b c : Bool) (k : Segment)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {outside : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (k.sweep w).active e B ((k.fixed w b c).map e.cells ∪ outside)) :
    Reachable B (some 1)
      (e.extend outside ⟨(k.sweep w).hub, andMixedBoxes w (stage w b c k.before)⟩)
      (e.extend outside ⟨(k.sweep w).hub, andMixedBoxes w (stage w b c k.after)⟩) := by
  have hr := (k.sweep w).forward_placed e F
  have hzero := extend_endpoint w b c false k e outside
  change e.extend ((k.fixed w b c).map e.cells ∪ outside)
    ⟨(k.sweep w).hub, Finset.univ.image ((k.sweep w).position 0)⟩ =
    e.extend outside ⟨(k.sweep w).hub, andMixedBoxes w (stage w b c k.before)⟩ at hzero
  have hfull := extend_endpoint w b c true k e outside
  change e.extend ((k.fixed w b c).map e.cells ∪ outside)
    ⟨(k.sweep w).hub, Finset.univ.image ((k.sweep w).position (k.count w))⟩ =
    e.extend outside ⟨(k.sweep w).hub, andMixedBoxes w (stage w b c k.after)⟩ at hfull
  change Reachable B (some 1)
    (e.extend _ ⟨(k.sweep w).hub, Finset.univ.image ((k.sweep w).position 0)⟩)
    (e.extend _ ⟨(k.sweep w).hub, Finset.univ.image ((k.sweep w).position (k.count w))⟩) at hr
  rw [hzero, hfull] at hr
  exact hr

theorem backward_placed (w : ℕ) (b c : Bool) (k : Segment)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {outside : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (k.sweep w).active e B ((k.fixed w b c).map e.cells ∪ outside)) :
    Reachable B (some 1)
      (e.extend outside ⟨(k.sweep w).hub, andMixedBoxes w (stage w b c k.after)⟩)
      (e.extend outside ⟨(k.sweep w).hub, andMixedBoxes w (stage w b c k.before)⟩) := by
  have hr := (k.sweep w).backward_placed e F
  have hzero := extend_endpoint w b c false k e outside
  change e.extend ((k.fixed w b c).map e.cells ∪ outside)
    ⟨(k.sweep w).hub, Finset.univ.image ((k.sweep w).position 0)⟩ =
    e.extend outside ⟨(k.sweep w).hub, andMixedBoxes w (stage w b c k.before)⟩ at hzero
  have hfull := extend_endpoint w b c true k e outside
  change e.extend ((k.fixed w b c).map e.cells ∪ outside)
    ⟨(k.sweep w).hub, Finset.univ.image ((k.sweep w).position (k.count w))⟩ =
    e.extend outside ⟨(k.sweep w).hub, andMixedBoxes w (stage w b c k.after)⟩ at hfull
  change Reachable B (some 1)
    (e.extend _ ⟨(k.sweep w).hub, Finset.univ.image ((k.sweep w).position (k.count w))⟩)
    (e.extend _ ⟨(k.sweep w).hub, Finset.univ.image ((k.sweep w).position 0)⟩) at hr
  rw [hfull, hzero] at hr
  exact hr

/-- Travel along a straight stage's exposed lane with its complete mixed inventory fixed. -/
theorem lane_walk (w : ℕ) (hw : 2 ≤ w) (b c q : Bool) (k : Segment)
    (goals : Finset (Cell (side w) (side w))) (a d : Fin (side w))
    (ha : (k.sweep w).line.laneSegment a) (hd : (k.sweep w).line.laneSegment d) :
    Reachable (andBoard w goals) (some 1)
      ⟨(k.sweep w).map (a, (k.sweep w).line.lane), andMixedBoxes w (stage w b c (k.endpoint q))⟩
      ⟨(k.sweep w).map (d, (k.sweep w).line.lane), andMixedBoxes w (stage w b c (k.endpoint q))⟩ := by
  have hr := (k.frame w hw b c goals).lane_walk (if q then k.count w else 0) a d ha hd
  rw [k.boxes_endpoint w b c q] at hr
  exact hr

end PushPuzzle.PushS.FiniteGateAStraight.Segment
