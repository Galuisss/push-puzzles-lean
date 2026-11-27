/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateBranchSweeps
public import PushS.FiniteInventoryAtoms
public import PushS.FiniteMouthFrames

/-! Complete OR A-branch programs on ambient boards with exposed input and output faces. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateOrAAmbient

open PushFS FiniteGeometry FiniteGateMacros FiniteGateInputs FiniteGateBranchSweeps

variable {W H : ℕ}

attribute [local irreducible] side

def backwardActive (w : ℕ) : Finset (Cell (side w) (side w)) :=
  FiniteParallelFrames.active (point w 1 0).1 (point w 1 0).1
    (point w 2 0).1 (point w 3 0).1 (point w 0 1).2 (point w 0 0).2

def forwardActive (w mouth : ℕ) (hm : mouth ≤ w+8) : Finset (Cell (side w) (side w)) :=
  FiniteMouthFrames.leftActive (point w mouth 0 hm).1 (point w 2 0).1
    (point w 0 1).2 (point w 0 0).2

private theorem trigger_mem (w : ℕ) (b c : Bool) : point w 2 0 ∈ orBoxes w true b c := by
  have he : orCell w true b c .triggerA = point w 2 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]
  rw [← he]
  exact Finset.mem_image.mpr ⟨.triggerA, Finset.mem_univ _, rfl⟩

/-- Release A and restore the complete ordinary left branch under narrow ambient frames. -/
theorem or_A_backward (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (FT : FiniteWireFrame.Frame (backwardActive w) e B
      (((orBoxes w true b c).erase (point w 2 0)).map e.cells ∪ extra))
    (FL : FiniteWireFrame.Frame (orInputSweep w).active e B
      ((orInputFixed w b c).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 1 1,orBoxes w true b c⟩)
      (e.extend extra ⟨point w 1 1,orBoxes w false b c⟩) := by
  have hr := FiniteParallelFrames.update_ambient
    (point w 1 0).1 (point w 1 0).1 (point w 2 0).1 (point w 3 0).1
    (point w 0 1).2 (point w 0 0).2 .south .east
    (by dsimp [Adjacent, point]; unfold origin; omega)
    (by dsimp [Adjacent, Direction.opposite, point]; unfold origin; omega)
    (by dsimp [Adjacent, point]; omega) (by dsimp [Adjacent, point]; omega)
    (orBoxes w true b c) (trigger_mem w b c) e FT
  have hfirst : Reachable B (some 1)
      (e.extend extra ⟨point w 1 1,orBoxes w true b c⟩)
      (e.extend extra ⟨point w 1 1,orInputBoxes w b c true⟩) := by
    rw [← orInputBoxes_true w hw b c]
    exact hr
  exact hfirst.trans (FiniteGateBranchSweeps.or_A_tail_backward w b c e FL)

/-- The prepared trigger enters through its real selected B-side or C-side mouth. -/
theorem or_A_finish (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (mouth : ℕ) (hm : mouth ≤ w+8) (hgap : 4 ≤ mouth)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (forwardActive w mouth hm) e B
      (((orBoxes w true b c).erase (point w 2 0)).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w mouth 1 hm,orInputBoxes w b c true⟩)
      (e.extend extra ⟨point w mouth 1 hm,orBoxes w true b c⟩) := by
  rw [← orInputBoxes_true w hw b c]
  exact FiniteMouthFrames.left_restore_ambient
    (point w mouth 0 hm).1 (point w 4 0).1 (point w 3 0).1 (point w 2 0).1
    (point w 0 1).2 (point w 0 0).2
    (by dsimp [Adjacent, point]; unfold origin; omega)
    (by dsimp [Adjacent, point]; omega) (by dsimp [Adjacent, point]; omega)
    (by dsimp [point]; omega) (orBoxes w true b c) (trigger_mem w b c) e F

/-- Complete A while leaving only travel between its exposed left and selected mouth faces. -/
theorem or_A_forward (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (mouth : ℕ) (hm : mouth ≤ w+8) (hgap : 4 ≤ mouth)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (FL : FiniteWireFrame.Frame (orInputSweep w).active e B
      ((orInputFixed w b c).map e.cells ∪ extra))
    (FT : FiniteWireFrame.Frame (forwardActive w mouth hm) e B
      (((orBoxes w true b c).erase (point w 2 0)).map e.cells ∪ extra))
    (hface : Reachable B (some 1)
      (e.extend extra ⟨point w 1 1,orInputBoxes w b c true⟩)
      (e.extend extra ⟨point w mouth 1 hm,orInputBoxes w b c true⟩)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 1 1,orBoxes w false b c⟩)
      (e.extend extra ⟨point w mouth 1 hm,orBoxes w true b c⟩) :=
  (FiniteGateBranchSweeps.or_A_tail_forward w b c e FL).trans
    (hface.trans (or_A_finish w hw b c mouth hm hgap e FT))

/-- With B open, the complete forward program uses only its short exposed upper-row connector. -/
theorem or_A_forward_B (w : ℕ) (hw : 2 ≤ w) (c : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (FL : FiniteWireFrame.Frame (orInputSweep w).active e B
      ((orInputFixed w true c).map e.cells ∪ extra))
    (FT : FiniteWireFrame.Frame (forwardActive w 4 (by omega)) e B
      (((orBoxes w true true c).erase (point w 2 0)).map e.cells ∪ extra))
    (FW : FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (point w 1 1) (point w 4 1)) e B
      ((orInputBoxes w true c true).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 1 1,orBoxes w false true c⟩)
      (e.extend extra ⟨point w 4 1,orBoxes w true true c⟩) :=
  or_A_forward w hw true c 4 (by omega) (by omega) e FL FT
    (FiniteAtomFrames.walk_ambient _ _ e FW)

end PushPuzzle.PushS.FiniteGateOrAAmbient
