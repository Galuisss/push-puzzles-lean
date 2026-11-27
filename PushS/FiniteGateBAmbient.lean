/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateBranchSweeps
public import PushS.FiniteInventoryAtoms
public import PushS.FiniteGateBTemporary
public import PushS.FiniteMouthFrames
import Mathlib.Tactic.Tauto

/-! Actual ambient B-branch propagation, its finite cavity approaches, and the temporary A double push. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateBAmbient

open PushFS FiniteGeometry FiniteGateMacros FiniteGateVertical FiniteGateBranchSweeps
open FiniteGateBTemporary

variable {W H : ℕ}

attribute [local irreducible] side

def downLocalActive (w column : ℕ) (hc : 3 ≤ column ∧ column ≤ 4) :
    Finset (Cell (side w) (side w)) :=
  FiniteParallelFrames.active (point w 0 2).2 (point w 0 3).2
    (point w 0 2).2 (point w 0 1).2
    (point w (column-1) 0 (by omega)).1 (point w column 0 (by omega)).1

/-- The downward trigger's three vertical cells and its two-cell left walking lane. -/
def backwardActive (w column : ℕ) (hc : 3 ≤ column ∧ column ≤ 4) :
    Finset (Cell (side w) (side w)) :=
  (downLocalActive w column hc).map (GridIsometry.transpose (side w) (side w)).embedding.cells

/-- The three cells of the prepared B lift. -/
def raiseActive (w column : ℕ) (hc : column ≤ 4) : Finset (Cell (side w) (side w)) :=
  FiniteAtomFrames.pushActive (point w column 0 (by omega))
    (point w column 1 (by omega)) (point w column 2 (by omega))

/-- The actual two-cell horizontal exit after the B lift. -/
def exitActive (w column : ℕ) (hc : 3 ≤ column ∧ column ≤ 4) : Finset (Cell (side w) (side w)) :=
  FiniteAtomFrames.walkActive (point w column 1 (by omega)) (point w (column-1) 1 (by omega))

/-- Enter from above a real cavity mouth and follow its row to B's support. -/
def entryActive (w mouth column : ℕ) (hm : mouth ≤ w+8) (hc : column ≤ 4) :
    Finset (Cell (side w) (side w)) :=
  FiniteAtomFrames.walkActive (point w mouth 1 hm) (point w mouth 0 hm) ∪
  FiniteAtomFrames.walkActive (point w mouth 0 hm) (point w column 0 (by omega))

/-- Follow a finite L-shaped actual cavity entrance, with its complete stock fixed. -/
private theorem enter (w mouth column : ℕ) (hm : mouth ≤ w+8) (hc : column ≤ 4)
    (stock : Finset (Cell (side w) (side w)))
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (entryActive w mouth column hm hc) e B
      (stock.map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w mouth 1 hm,stock⟩)
      (e.extend extra ⟨point w column 0 (by omega),stock⟩) := by
  have h1 := FiniteAtomFrames.walk_ambient (point w mouth 1 hm) (point w mouth 0 hm) e
    (F.mono_active Finset.subset_union_left)
  have h2 := FiniteAtomFrames.walk_ambient (point w mouth 0 hm) (point w column 0 (by omega)) e
    (F.mono_active Finset.subset_union_right)
  exact h1.trans h2

/-- Lift a prepared B boundary and follow its real left exit. -/
private theorem raise (w column : ℕ) (hc : 3 ≤ column ∧ column ≤ 4)
    (target : Finset (Cell (side w) (side w))) (hnext : point w column 2 (by omega) ∈ target)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (FP : FiniteWireFrame.Frame (raiseActive w column hc.2) e B
      ((target.erase (point w column 2 (by omega))).map e.cells ∪ extra))
    (FE : FiniteWireFrame.Frame (exitActive w column hc) e B (target.map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w column 0 (by omega),
        insert (point w column 1 (by omega)) (target.erase (point w column 2 (by omega)))⟩)
      (e.extend extra ⟨point w (column-1) 1 (by omega),target⟩) := by
  have hp := FiniteAtomFrames.restore_ambient
    (point w column 0 (by omega)) (point w column 1 (by omega))
    (point w column 2 (by omega)) .north
    (by dsimp [Adjacent, point]; unfold origin; omega)
    (by dsimp [Adjacent, point]; unfold origin; omega) target hnext e FP
  exact hp.trans (FiniteAtomFrames.walk_ambient _ _ e FE)

private theorem down (w column : ℕ) (hc : 3 ≤ column ∧ column ≤ 4)
    (stock : Finset (Cell (side w) (side w))) (hsrc : point w column 2 (by omega) ∈ stock)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (backwardActive w column hc) e B
      ((stock.erase (point w column 2 (by omega))).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w (column-1) 2 (by omega),stock⟩)
      (e.extend extra ⟨point w (column-1) 2 (by omega),
        insert (point w column 1 (by omega)) (stock.erase (point w column 2 (by omega)))⟩) := by
  let a := (GridIsometry.transpose (side w) (side w)).embedding
  have F' : FiniteWireFrame.Frame (downLocalActive w column hc) (a.trans e) B
      ((stock.erase (point w column 2 (by omega))).map e.cells ∪ extra) := {
    floor p hp := F.floor (a.cells p) (Finset.mem_map.mpr ⟨p,hp,rfl⟩)
    fixed_avoids p hp := F.fixed_avoids (a.cells p) (Finset.mem_map.mpr ⟨p,hp,rfl⟩)
    fixed_floor := F.fixed_floor }
  exact FiniteParallelFrames.update_mapped_ambient
    (point w 0 2).2 (point w 0 3).2 (point w 0 2).2 (point w 0 1).2
    (point w (column-1) 0 (by omega)).1 (point w column 0 (by omega)).1 .south .east
    (by dsimp [Adjacent, point]; omega)
    (by dsimp [Adjacent, Direction.opposite, point]; omega)
    (by dsimp [Adjacent, point]; unfold origin; omega)
    (by dsimp [Adjacent, point]; unfold origin; omega) a stock hsrc e F'

private theorem and_B_mem (w : ℕ) (a c : Bool) : point w 3 2 ∈ andBoxes w a true c := by
  have he : andCell w a true c (.branchB 0) = point w 3 2 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]; omega
  rw [← he]
  exact Finset.mem_image.mpr ⟨.branchB 0,Finset.mem_univ _,rfl⟩

/-- Release B and restore every ordinary upper-tail box on the ambient board. -/
theorem and_B_backward (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (FT : FiniteWireFrame.Frame (backwardActive w 3 (by omega)) e B
      (((andBoxes w a true c).erase (point w 3 2)).map e.cells ∪ extra))
    (FL : FiniteWireFrame.Frame (andBSweep w).active e B
      ((andBFixed w a c).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 2 2,andBoxes w a true c⟩)
      (e.extend extra ⟨point w 2 2,andBoxes w a false c⟩) := by
  have hr := down w 3 (by omega) (andBoxes w a true c) (and_B_mem w a c) e FT
  rw [andBBoxes_prepared w hw a c] at hr
  exact hr.trans (FiniteGateBranchSweeps.and_B_tail_backward w a c e FL)

/-- Lift B after its entire ordinary tail has reached the prepared phase. -/
theorem and_B_raise (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (FP : FiniteWireFrame.Frame (raiseActive w 3 (by omega)) e B
      (((andBoxes w a true c).erase (point w 3 2)).map e.cells ∪ extra))
    (FE : FiniteWireFrame.Frame (exitActive w 3 (by omega)) e B
      ((andBoxes w a true c).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 3 0,andBBoxes w a c true⟩)
      (e.extend extra ⟨point w 2 1,andBoxes w a true c⟩) := by
  rw [← andBBoxes_prepared w hw a c]
  exact raise w 3 (by omega) (andBoxes w a true c) (and_B_mem w a c) e FP FE

/-- Complete B with one exposed-face connection and the finite cavity approach supplied explicitly. -/
theorem and_B_forward (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (mouth : ℕ) (hm : mouth ≤ w+8)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (FL : FiniteWireFrame.Frame (andBSweep w).active e B
      ((andBFixed w a c).map e.cells ∪ extra))
    (FA : FiniteWireFrame.Frame (entryActive w mouth 3 hm (by omega)) e B
      ((andBBoxes w a c true).map e.cells ∪ extra))
    (FP : FiniteWireFrame.Frame (raiseActive w 3 (by omega)) e B
      (((andBoxes w a true c).erase (point w 3 2)).map e.cells ∪ extra))
    (FE : FiniteWireFrame.Frame (exitActive w 3 (by omega)) e B
      ((andBoxes w a true c).map e.cells ∪ extra))
    (hface : Reachable B (some 1)
      (e.extend extra ⟨point w 2 2,andBBoxes w a c true⟩)
      (e.extend extra ⟨point w mouth 1 hm,andBBoxes w a c true⟩)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 2 2,andBoxes w a false c⟩)
      (e.extend extra ⟨point w 2 1,andBoxes w a true c⟩) :=
  (FiniteGateBranchSweeps.and_B_tail_forward w a c e FL).trans
    (hface.trans ((enter w mouth 3 hm (by omega) (andBBoxes w a c true) e FA).trans
      (and_B_raise w hw a c e FP FE)))

private theorem or_B_mem (w : ℕ) (a c : Bool) : point w 4 2 ∈ orBoxes w a true c := by
  have he : orCell w a true c (.branchB 0) = point w 4 2 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]; omega
  rw [← he]
  exact Finset.mem_image.mpr ⟨.branchB 0,Finset.mem_univ _,rfl⟩

/-- Release B and restore every ordinary upper-tail box on the ambient board. -/
theorem or_B_backward (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (FT : FiniteWireFrame.Frame (backwardActive w 4 (by omega)) e B
      (((orBoxes w a true c).erase (point w 4 2)).map e.cells ∪ extra))
    (FL : FiniteWireFrame.Frame (orBSweep w).active e B
      ((orBFixed w a c).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 3 2,orBoxes w a true c⟩)
      (e.extend extra ⟨point w 3 2,orBoxes w a false c⟩) := by
  have hr := down w 4 (by omega) (orBoxes w a true c) (or_B_mem w a c) e FT
  rw [orBBoxes_prepared w hw a c] at hr
  exact hr.trans (FiniteGateBranchSweeps.or_B_tail_backward w a c e FL)

/-- Lift B after its entire ordinary tail has reached the prepared phase. -/
private theorem or_B_raise (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (FP : FiniteWireFrame.Frame (raiseActive w 4 (by omega)) e B
      (((orBoxes w a true c).erase (point w 4 2)).map e.cells ∪ extra))
    (FE : FiniteWireFrame.Frame (exitActive w 4 (by omega)) e B
      ((orBoxes w a true c).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 4 0,orBBoxes w a c true⟩)
      (e.extend extra ⟨point w 3 1,orBoxes w a true c⟩) := by
  rw [← orBBoxes_prepared w hw a c]
  exact raise w 4 (by omega) (orBoxes w a true c) (or_B_mem w a c) e FP FE

/-- Complete B with one exposed-face connection and the finite cavity approach supplied explicitly. -/
theorem or_B_forward (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (mouth : ℕ) (hm : mouth ≤ w+8)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (FL : FiniteWireFrame.Frame (orBSweep w).active e B
      ((orBFixed w a c).map e.cells ∪ extra))
    (FA : FiniteWireFrame.Frame (entryActive w mouth 4 hm (by omega)) e B
      ((orBBoxes w a c true).map e.cells ∪ extra))
    (FP : FiniteWireFrame.Frame (raiseActive w 4 (by omega)) e B
      (((orBoxes w a true c).erase (point w 4 2)).map e.cells ∪ extra))
    (FE : FiniteWireFrame.Frame (exitActive w 4 (by omega)) e B
      ((orBoxes w a true c).map e.cells ∪ extra))
    (hface : Reachable B (some 1)
      (e.extend extra ⟨point w 3 2,orBBoxes w a c true⟩)
      (e.extend extra ⟨point w mouth 1 hm,orBBoxes w a c true⟩)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 3 2,orBoxes w a false c⟩)
      (e.extend extra ⟨point w 3 1,orBoxes w a true c⟩) :=
  (FiniteGateBranchSweeps.or_B_tail_forward w a c e FL).trans
    (hface.trans ((enter w mouth 4 hm (by omega) (orBBoxes w a c true) e FA).trans
      (or_B_raise w hw a c e FP FE)))

private theorem temporary_prepared (w : ℕ) (hw : 2 ≤ w) :
    insert (point w 4 0) ((andBBoxes w false false true).erase (point w 3 0)) =
      insert (point w 3 1) ((temporaryBoxes w).erase (point w 3 2)) := by
  rw [← andBBoxes_prepared w hw false false]
  have hBA : point w 3 1 ≠ point w 3 0 := by
    intro he
    have hy := congrArg (fun p => p.2.val) he
    dsimp [point] at hy
    unfold origin at hy
    omega
  have hAB : point w 4 0 ≠ point w 3 2 := by
    intro he
    have hx := congrArg (fun p => p.1.val) he
    dsimp [point] at hx
    omega
  unfold temporaryBoxes
  rw [Finset.erase_insert_of_ne hBA, Finset.erase_insert_of_ne hAB]
  ext p
  simp only [Finset.mem_insert, Finset.mem_erase]
  tauto

private theorem temporary_B_mem (w : ℕ) : point w 3 2 ∈ temporaryBoxes w := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_erase.mpr
  constructor
  · intro he
    have hy := congrArg (fun p => p.2.val) he
    dsimp [point] at hy
    unfold origin at hy
    omega
  · exact and_B_mem w false false

/-- Temporarily move A aside and immediately lift B from the actual support reached. -/
private theorem and_B_raise_closedA (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (FA : FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (point w 2 2) (point w 2 0)) e B
      ((andBBoxes w false false true).map e.cells ∪ extra))
    (FP : FiniteWireFrame.Frame
      (FiniteAtomFrames.pushActive (point w 2 0) (point w 3 0) (point w 4 0)) e B
      (((andBBoxes w false false true).erase (point w 3 0)).map e.cells ∪ extra))
    (FB : FiniteWireFrame.Frame (raiseActive w 3 (by omega)) e B
      (((temporaryBoxes w).erase (point w 3 2)).map e.cells ∪ extra))
    (FE : FiniteWireFrame.Frame (exitActive w 3 (by omega)) e B
      ((temporaryBoxes w).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 2 2,andBBoxes w false false true⟩)
      (e.extend extra ⟨point w 2 1,temporaryBoxes w⟩) := by
  have hA : point w 3 0 ∈ andBBoxes w false false true := by
    have he : andBCell w false false true .triggerA = point w 3 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [andBCell, andCell, andPoint, point]
    rw [← he]
    exact Finset.mem_image.mpr ⟨.triggerA,Finset.mem_univ _,rfl⟩
  have hp := FiniteAtomFrames.update_ambient (point w 2 0) (point w 3 0) (point w 4 0) .east
    (by dsimp [Adjacent, point]; omega) (by dsimp [Adjacent, point]; omega)
    (andBBoxes w false false true) hA e FP
  rw [temporary_prepared w hw] at hp
  have hb := raise w 3 (by omega) (temporaryBoxes w) (temporary_B_mem w) e FB FE
  exact (FiniteAtomFrames.walk_ambient _ _ e FA).trans (hp.trans hb)

/-- Restore the temporarily moved A through its true right cavity mouth. -/
theorem and_B_restore_A (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame
      (FiniteMouthFrames.leftActive (point w (w+4) 0).1 (point w 3 0).1
        (point w 0 1).2 (point w 0 0).2) e B
      (((andBoxes w false true false).erase (point w 3 0)).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w (w+4) 1,temporaryBoxes w⟩)
      (e.extend extra ⟨point w (w+4) 1,andBoxes w false true false⟩) := by
  have hA : point w 3 0 ∈ andBoxes w false true false := by
    have he : andCell w false true false .triggerA = point w 3 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]
    rw [← he]
    exact Finset.mem_image.mpr ⟨.triggerA,Finset.mem_univ _,rfl⟩
  exact FiniteMouthFrames.left_restore_ambient
    (point w (w+4) 0).1 (point w 5 0).1 (point w 4 0).1 (point w 3 0).1
    (point w 0 1).2 (point w 0 0).2
    (by dsimp [Adjacent, point]; unfold origin; omega)
    (by dsimp [Adjacent, point]; omega) (by dsimp [Adjacent, point]; omega)
    (by dsimp [point]; omega) (andBoxes w false true false) hA e F

/-- Complete the closed-A B branch, including its two actual temporary A pushes. -/
theorem and_B_forward_closedA (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (FL : FiniteWireFrame.Frame (andBSweep w).active e B
      ((andBFixed w false false).map e.cells ∪ extra))
    (FA : FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (point w 2 2) (point w 2 0)) e B
      ((andBBoxes w false false true).map e.cells ∪ extra))
    (FP : FiniteWireFrame.Frame
      (FiniteAtomFrames.pushActive (point w 2 0) (point w 3 0) (point w 4 0)) e B
      (((andBBoxes w false false true).erase (point w 3 0)).map e.cells ∪ extra))
    (FB : FiniteWireFrame.Frame (raiseActive w 3 (by omega)) e B
      (((temporaryBoxes w).erase (point w 3 2)).map e.cells ∪ extra))
    (FE : FiniteWireFrame.Frame (exitActive w 3 (by omega)) e B
      ((temporaryBoxes w).map e.cells ∪ extra))
    (FR : FiniteWireFrame.Frame
      (FiniteMouthFrames.leftActive (point w (w+4) 0).1 (point w 3 0).1
        (point w 0 1).2 (point w 0 0).2) e B
      (((andBoxes w false true false).erase (point w 3 0)).map e.cells ∪ extra))
    (hface : Reachable B (some 1)
      (e.extend extra ⟨point w 2 1,temporaryBoxes w⟩)
      (e.extend extra ⟨point w (w+4) 1,temporaryBoxes w⟩)) :
    Reachable B (some 1)
      (e.extend extra ⟨point w 2 2,andBoxes w false false false⟩)
      (e.extend extra ⟨point w (w+4) 1,andBoxes w false true false⟩) :=
  (FiniteGateBranchSweeps.and_B_tail_forward w false false e FL).trans
    ((and_B_raise_closedA w hw e FA FP FB FE).trans (hface.trans (and_B_restore_A w hw e FR)))

end PushPuzzle.PushS.FiniteGateBAmbient
