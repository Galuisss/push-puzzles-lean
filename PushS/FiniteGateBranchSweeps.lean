/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteStockSweep
public import PushS.FiniteGateOutputs
public import PushS.FiniteGateInputs
public import PushS.FiniteGateVertical

/-! Ambient straight stock propagation on all remaining thick gate branches. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateBranchSweeps

open PushFS FiniteGeometry FiniteSquareLine FiniteGateOutputs FiniteGateInputs
open FiniteGateVertical FiniteGateMacros

variable {W H : ℕ}

attribute [local irreducible] side

def andOutputSweep (w : ℕ) : Sweep (side w) := ⟨outputLine w 6,false⟩

theorem andOutputSweep_hub (w : ℕ) : (andOutputSweep w).hub = point w (w+6) 1 := by
  apply Prod.ext <;> apply Fin.ext <;>
    dsimp [andOutputSweep, Sweep.hub, Sweep.map, outputLine, point]

private theorem andOutputSweep_stock (w : ℕ) (a b q : Bool) :
    (andOutputSweep w).boxes (andOutputFixed w a b) (if q then (andOutputSweep w).line.count else 0) =
      andOutputBoxes w a b q := by
  exact andOutputLine_boxes w a b q

/-- Complete forward propagation of the branch stock through its narrow ambient frame. -/
theorem and_C_tail_forward (w : ℕ) (a b : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (andOutputSweep w).active e B
      ((andOutputFixed w a b).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w (w+6) 1, andOutputBoxes w a b false⟩)
      (e.extend extra ⟨point w (w+6) 1, andBoxes w a b true⟩) := by
  have hr := (andOutputSweep w).stock_forward (andOutputFixed w a b)
    (andOutputBoxes w a b) (andOutputSweep_stock w a b) e F
  simpa only [andOutputSweep_hub, andOutputBoxes_true] using hr

/-- Complete backward propagation of the branch stock through its narrow ambient frame. -/
theorem and_C_tail_backward (w : ℕ) (a b : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (andOutputSweep w).active e B
      ((andOutputFixed w a b).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w (w+6) 1, andBoxes w a b true⟩)
      (e.extend extra ⟨point w (w+6) 1, andOutputBoxes w a b false⟩) := by
  have hr := (andOutputSweep w).stock_backward (andOutputFixed w a b)
    (andOutputBoxes w a b) (andOutputSweep_stock w a b) e F
  simpa only [andOutputSweep_hub, andOutputBoxes_true] using hr

def orOutputSweep (w : ℕ) : Sweep (side w) := ⟨outputLine w 7,false⟩

theorem orOutputSweep_hub (w : ℕ) : (orOutputSweep w).hub = point w (w+7) 1 := by
  apply Prod.ext <;> apply Fin.ext <;>
    dsimp [orOutputSweep, Sweep.hub, Sweep.map, outputLine, point]

private theorem orOutputSweep_stock (w : ℕ) (a b q : Bool) :
    (orOutputSweep w).boxes (orOutputFixed w a b) (if q then (orOutputSweep w).line.count else 0) =
      orOutputBoxes w a b q := by
  exact orOutputLine_boxes w a b q

/-- Complete forward propagation of the branch stock through its narrow ambient frame. -/
theorem or_C_tail_forward (w : ℕ) (a b : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (orOutputSweep w).active e B
      ((orOutputFixed w a b).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w (w+7) 1, orOutputBoxes w a b false⟩)
      (e.extend extra ⟨point w (w+7) 1, orBoxes w a b true⟩) := by
  have hr := (orOutputSweep w).stock_forward (orOutputFixed w a b)
    (orOutputBoxes w a b) (orOutputSweep_stock w a b) e F
  simpa only [orOutputSweep_hub, orOutputBoxes_true] using hr

/-- Complete backward propagation of the branch stock through its narrow ambient frame. -/
theorem or_C_tail_backward (w : ℕ) (a b : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (orOutputSweep w).active e B
      ((orOutputFixed w a b).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w (w+7) 1, orBoxes w a b true⟩)
      (e.extend extra ⟨point w (w+7) 1, orOutputBoxes w a b false⟩) := by
  have hr := (orOutputSweep w).stock_backward (orOutputFixed w a b)
    (orOutputBoxes w a b) (orOutputSweep_stock w a b) e F
  simpa only [orOutputSweep_hub, orOutputBoxes_true] using hr

def orInputSweep (w : ℕ) : Sweep (side w) := ⟨orInputLine w,false⟩

theorem orInputSweep_hub (w : ℕ) : (orInputSweep w).hub = point w 1 1 := by
  apply Prod.ext <;> apply Fin.ext <;>
    dsimp [orInputSweep, Sweep.hub, Sweep.map, orInputLine, point]

private theorem orInputSweep_stock (w : ℕ) (b c q : Bool) :
    (orInputSweep w).boxes (orInputFixed w b c) (if q then (orInputSweep w).line.count else 0) =
      orInputBoxes w b c q := by
  exact orInputLine_boxes w b c q

/-- Complete forward propagation of the branch stock through its narrow ambient frame. -/
theorem or_A_tail_forward (w : ℕ) (b c : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (orInputSweep w).active e B
      ((orInputFixed w b c).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 1 1, orBoxes w false b c⟩)
      (e.extend extra ⟨point w 1 1, orInputBoxes w b c true⟩) := by
  have hr := (orInputSweep w).stock_forward (orInputFixed w b c)
    (orInputBoxes w b c) (orInputSweep_stock w b c) e F
  simpa only [orInputSweep_hub, orInputBoxes_false] using hr

/-- Complete backward propagation of the branch stock through its narrow ambient frame. -/
theorem or_A_tail_backward (w : ℕ) (b c : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (orInputSweep w).active e B
      ((orInputFixed w b c).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 1 1, orInputBoxes w b c true⟩)
      (e.extend extra ⟨point w 1 1, orBoxes w false b c⟩) := by
  have hr := (orInputSweep w).stock_backward (orInputFixed w b c)
    (orInputBoxes w b c) (orInputSweep_stock w b c) e F
  simpa only [orInputSweep_hub, orInputBoxes_false] using hr

def andBSweep (w : ℕ) : Sweep (side w) := ⟨inputBLine w (4*w+15) 3,true⟩

theorem andBSweep_hub (w : ℕ) : (andBSweep w).hub = point w 2 2 := by
  apply Prod.ext <;> apply Fin.ext <;>
    dsimp [andBSweep, Sweep.hub, Sweep.map, inputBLine, point]

private theorem andBSweep_stock (w : ℕ) (a c q : Bool) :
    (andBSweep w).boxes (andBFixed w a c) (if q then (andBSweep w).line.count else 0) =
      andBBoxes w a c q := by
  exact andBLine_boxes w a c q

/-- Complete forward propagation of the branch stock through its narrow ambient frame. -/
theorem and_B_tail_forward (w : ℕ) (a c : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (andBSweep w).active e B
      ((andBFixed w a c).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 2 2, andBoxes w a false c⟩)
      (e.extend extra ⟨point w 2 2, andBBoxes w a c true⟩) := by
  have hr := (andBSweep w).stock_forward (andBFixed w a c)
    (andBBoxes w a c) (andBSweep_stock w a c) e F
  simpa only [andBSweep_hub, andBBoxes_false] using hr

/-- Complete backward propagation of the branch stock through its narrow ambient frame. -/
theorem and_B_tail_backward (w : ℕ) (a c : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (andBSweep w).active e B
      ((andBFixed w a c).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 2 2, andBBoxes w a c true⟩)
      (e.extend extra ⟨point w 2 2, andBoxes w a false c⟩) := by
  have hr := (andBSweep w).stock_backward (andBFixed w a c)
    (andBBoxes w a c) (andBSweep_stock w a c) e F
  simpa only [andBSweep_hub, andBBoxes_false] using hr

def orBSweep (w : ℕ) : Sweep (side w) := ⟨inputBLine w (w+6) 4,true⟩

theorem orBSweep_hub (w : ℕ) : (orBSweep w).hub = point w 3 2 := by
  apply Prod.ext <;> apply Fin.ext <;>
    dsimp [orBSweep, Sweep.hub, Sweep.map, inputBLine, point]

private theorem orBSweep_stock (w : ℕ) (a c q : Bool) :
    (orBSweep w).boxes (orBFixed w a c) (if q then (orBSweep w).line.count else 0) =
      orBBoxes w a c q := by
  exact orBLine_boxes w a c q

/-- Complete forward propagation of the branch stock through its narrow ambient frame. -/
theorem or_B_tail_forward (w : ℕ) (a c : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (orBSweep w).active e B
      ((orBFixed w a c).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 3 2, orBoxes w a false c⟩)
      (e.extend extra ⟨point w 3 2, orBBoxes w a c true⟩) := by
  have hr := (orBSweep w).stock_forward (orBFixed w a c)
    (orBBoxes w a c) (orBSweep_stock w a c) e F
  simpa only [orBSweep_hub, orBBoxes_false] using hr

/-- Complete backward propagation of the branch stock through its narrow ambient frame. -/
theorem or_B_tail_backward (w : ℕ) (a c : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (orBSweep w).active e B
      ((orBFixed w a c).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 3 2, orBBoxes w a c true⟩)
      (e.extend extra ⟨point w 3 2, orBoxes w a false c⟩) := by
  have hr := (orBSweep w).stock_backward (orBFixed w a c)
    (orBBoxes w a c) (orBSweep_stock w a c) e F
  simpa only [orBSweep_hub, orBBoxes_false] using hr

end PushPuzzle.PushS.FiniteGateBranchSweeps
