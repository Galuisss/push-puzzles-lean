/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateBranchSweeps
public import PushS.FiniteInventoryAtoms
public import PushS.FiniteRightMouthFrames

/-! Complete ambient C-branch programs with only the actual input-side face connection exposed. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateCAmbient

open PushFS FiniteGeometry FiniteGateMacros FiniteGateOutputs FiniteGateBranchSweeps

variable {W H : ℕ}

attribute [local irreducible] side

/-- The C contraction uses three row cells and the two-cell upper lane to their right. -/
def forwardActive (w shift : ℕ) (hs : 6 ≤ shift ∧ shift ≤ 7) : Finset (Cell (side w) (side w)) :=
  FiniteParallelFrames.active (point w (w+shift) 0 (by omega)).1
    (point w (w+shift) 0 (by omega)).1
    (point w (w+shift-1) 0 (by omega)).1 (point w (w+shift-2) 0 (by omega)).1
    (point w 0 1).2 (point w 0 0).2

/-- The released output boundary is reached from its specified left input mouth. -/
def backwardActive (w mouth shift : ℕ) (hm : mouth ≤ 4) (hs : 6 ≤ shift ∧ shift ≤ 7) :
    Finset (Cell (side w) (side w)) :=
  FiniteMouthFrames.rightActive (point w mouth 0 (by omega)).1
    (point w (w+shift-1) 0 (by omega)).1 (point w 0 1).2 (point w 0 0).2

private theorem and_C_mem (w : ℕ) (a b : Bool) :
    point w (w+5) 0 ∈ andBoxes w a b false := by
  have he : andCell w a b false (.branchC 0) = point w (w+5) 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]; omega
  rw [← he]
  exact Finset.mem_image.mpr ⟨.branchC 0, Finset.mem_univ _, rfl⟩

/-- Push the first C box through its actual upper-lane support. -/
theorem and_C_first (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (forwardActive w 6 (by omega)) e B
      (((andBoxes w a b false).erase (point w (w+5) 0)).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w (w+6) 1, andBoxes w a b false⟩)
      (e.extend extra ⟨point w (w+6) 1, andOutputBoxes w a b false⟩) := by
  have hr := FiniteParallelFrames.update_ambient
    (point w (w+6) 0).1 (point w (w+6) 0).1
    (point w (w+5) 0).1 (point w (w+4) 0).1
    (point w 0 1).2 (point w 0 0).2 .south .west
    (by dsimp [Adjacent, point]; unfold origin; omega)
    (by dsimp [Adjacent, Direction.opposite, point]; unfold origin; omega)
    (by dsimp [Adjacent, point]; omega) (by dsimp [Adjacent, point]; omega)
    (andBoxes w a b false) (and_C_mem w a b) e F
  rw [← andOutputBoxes_initial w hw a b]
  exact hr

/-- Contract the complete C branch on the actual ambient board. -/
theorem and_C_forward (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (FF : FiniteWireFrame.Frame (forwardActive w 6 (by omega)) e B
      (((andBoxes w a b false).erase (point w (w+5) 0)).map e.cells ∪ extra))
    (FL : FiniteWireFrame.Frame (andOutputSweep w).active e B
      ((andOutputFixed w a b).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w (w+6) 1, andBoxes w a b false⟩)
      (e.extend extra ⟨point w (w+6) 1, andBoxes w a b true⟩) :=
  (and_C_first w hw a b e FF).trans
    (FiniteGateBranchSweeps.and_C_tail_forward w a b e FL)

/-- Release the prepared C trigger through a specified input-side mouth. -/
theorem and_C_release (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (mouth : ℕ) (hm : mouth ≤ 4) (hgap : mouth ≤ w+3)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (backwardActive w mouth 6 hm (by omega)) e B
      (((andBoxes w a b false).erase (point w (w+5) 0)).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w mouth 1 (by omega), andOutputBoxes w a b false⟩)
      (e.extend extra ⟨point w mouth 1 (by omega), andBoxes w a b false⟩) := by
  rw [← andOutputBoxes_initial w hw a b]
  exact FiniteMouthFrames.right_restore_ambient
    (point w mouth 0 (by omega)).1 (point w (w+3) 0).1
    (point w (w+4) 0).1 (point w (w+5) 0).1
    (point w 0 1).2 (point w 0 0).2
    (by dsimp [Adjacent, point]; unfold origin; omega)
    (by dsimp [Adjacent, point]; omega) (by dsimp [Adjacent, point]; omega)
    (by dsimp [point]; omega) (andBoxes w a b false) (and_C_mem w a b) e F

/-- Restore every C box, leaving only the explicit travel between its two exposed faces. -/
theorem and_C_backward (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (mouth : ℕ) (hm : mouth ≤ 4) (hgap : mouth ≤ w+3)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (FL : FiniteWireFrame.Frame (andOutputSweep w).active e B
      ((andOutputFixed w a b).map e.cells ∪ extra))
    (FR : FiniteWireFrame.Frame (backwardActive w mouth 6 hm (by omega)) e B
      (((andBoxes w a b false).erase (point w (w+5) 0)).map e.cells ∪ extra))
    (hface : Reachable B (some 1)
      (e.extend extra ⟨point w (w+6) 1, andOutputBoxes w a b false⟩)
      (e.extend extra ⟨point w mouth 1 (by omega), andOutputBoxes w a b false⟩)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w (w+6) 1, andBoxes w a b true⟩)
      (e.extend extra ⟨point w mouth 1 (by omega), andBoxes w a b false⟩) :=
  (FiniteGateBranchSweeps.and_C_tail_backward w a b e FL).trans
    (hface.trans (and_C_release w hw a b mouth hm hgap e FR))

private theorem or_C_mem (w : ℕ) (a b : Bool) :
    point w (w+6) 0 ∈ orBoxes w a b false := by
  have he : orCell w a b false (.branchC 0) = point w (w+6) 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]; omega
  rw [← he]
  exact Finset.mem_image.mpr ⟨.branchC 0, Finset.mem_univ _, rfl⟩

/-- Push the first C box through its actual upper-lane support. -/
theorem or_C_first (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (forwardActive w 7 (by omega)) e B
      (((orBoxes w a b false).erase (point w (w+6) 0)).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w (w+7) 1, orBoxes w a b false⟩)
      (e.extend extra ⟨point w (w+7) 1, orOutputBoxes w a b false⟩) := by
  have hr := FiniteParallelFrames.update_ambient
    (point w (w+7) 0).1 (point w (w+7) 0).1
    (point w (w+6) 0).1 (point w (w+5) 0).1
    (point w 0 1).2 (point w 0 0).2 .south .west
    (by dsimp [Adjacent, point]; unfold origin; omega)
    (by dsimp [Adjacent, Direction.opposite, point]; unfold origin; omega)
    (by dsimp [Adjacent, point]; omega) (by dsimp [Adjacent, point]; omega)
    (orBoxes w a b false) (or_C_mem w a b) e F
  rw [← orOutputBoxes_initial w hw a b]
  exact hr

/-- Contract the complete C branch on the actual ambient board. -/
theorem or_C_forward (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (FF : FiniteWireFrame.Frame (forwardActive w 7 (by omega)) e B
      (((orBoxes w a b false).erase (point w (w+6) 0)).map e.cells ∪ extra))
    (FL : FiniteWireFrame.Frame (orOutputSweep w).active e B
      ((orOutputFixed w a b).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w (w+7) 1, orBoxes w a b false⟩)
      (e.extend extra ⟨point w (w+7) 1, orBoxes w a b true⟩) :=
  (or_C_first w hw a b e FF).trans
    (FiniteGateBranchSweeps.or_C_tail_forward w a b e FL)

/-- Release the prepared C trigger through a specified input-side mouth. -/
theorem or_C_release (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (mouth : ℕ) (hm : mouth ≤ 4) (hgap : mouth ≤ w+4)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (backwardActive w mouth 7 hm (by omega)) e B
      (((orBoxes w a b false).erase (point w (w+6) 0)).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w mouth 1 (by omega), orOutputBoxes w a b false⟩)
      (e.extend extra ⟨point w mouth 1 (by omega), orBoxes w a b false⟩) := by
  rw [← orOutputBoxes_initial w hw a b]
  exact FiniteMouthFrames.right_restore_ambient
    (point w mouth 0 (by omega)).1 (point w (w+4) 0).1
    (point w (w+5) 0).1 (point w (w+6) 0).1
    (point w 0 1).2 (point w 0 0).2
    (by dsimp [Adjacent, point]; unfold origin; omega)
    (by dsimp [Adjacent, point]; omega) (by dsimp [Adjacent, point]; omega)
    (by dsimp [point]; omega) (orBoxes w a b false) (or_C_mem w a b) e F

/-- Restore every C box, leaving only the explicit travel between its two exposed faces. -/
theorem or_C_backward (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (mouth : ℕ) (hm : mouth ≤ 4) (hgap : mouth ≤ w+4)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (FL : FiniteWireFrame.Frame (orOutputSweep w).active e B
      ((orOutputFixed w a b).map e.cells ∪ extra))
    (FR : FiniteWireFrame.Frame (backwardActive w mouth 7 hm (by omega)) e B
      (((orBoxes w a b false).erase (point w (w+6) 0)).map e.cells ∪ extra))
    (hface : Reachable B (some 1)
      (e.extend extra ⟨point w (w+7) 1, orOutputBoxes w a b false⟩)
      (e.extend extra ⟨point w mouth 1 (by omega), orOutputBoxes w a b false⟩)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w (w+7) 1, orBoxes w a b true⟩)
      (e.extend extra ⟨point w mouth 1 (by omega), orBoxes w a b false⟩) :=
  (FiniteGateBranchSweeps.or_C_tail_backward w a b e FL).trans
    (hface.trans (or_C_release w hw a b mouth hm hgap e FR))

end PushPuzzle.PushS.FiniteGateCAmbient
