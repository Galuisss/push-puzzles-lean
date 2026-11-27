/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateBForward
import Mathlib.Tactic.Tauto

/-! The AND B update with the explicit temporary A3→4→3 pair. -/

public section
namespace PushPuzzle.PushS.FiniteGateBTemporary

open PushFS FiniteGeometry FiniteGateCore FiniteGateMacros FiniteGatePrepared
open FiniteGateVertical FiniteGateBTriggers FiniteGateBForward

attribute [local irreducible] side

/-- B is open and every auxiliary box is normal; A temporarily occupies column four. -/
@[expose] def temporaryBoxes (w : ℕ) : Finset (Cell (side w) (side w)) :=
  insert (point w 4 0) ((andBoxes w false true false).erase (point w 3 0))

private theorem normal_A_mem (w : ℕ) : point w 3 0 ∈ andBoxes w false true false := by
  have he : andCell w false true false .triggerA = point w 3 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]
  rw [← he]
  exact Finset.mem_image.mpr ⟨.triggerA, Finset.mem_univ _, rfl⟩

private theorem normal_B_mem (w : ℕ) : point w 3 2 ∈ andBoxes w false true false := by
  have he : andCell w false true false (.branchB 0) = point w 3 2 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]; omega
  rw [← he]
  exact Finset.mem_image.mpr ⟨.branchB 0, Finset.mem_univ _, rfl⟩

private theorem normal_row_free (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w))) (x : ℕ)
    (hx : x ≤ w+8) (hleft : 2 ≤ x) (hA : x ≠ 3) (hC : x < w+5) :
    Free (andBoard w goals) (andBoxes w false true false) (point w x 0 hx) := by
  apply and_row_free w hw false true false goals
  all_goals simp only [point, Bool.toNat_false]; omega

/-- The left approach stays on column two while A is in its closed normal slot. -/
theorem approach_free (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hx : p.1.val = origin w+2) (hy : p.2.val ≤ origin w) :
    Free (andBoard w goals) (andBBoxes w false false true) p := by
  apply andBBoxes_free w hw false false goals
  · refine ⟨and_core_floor w hw p (by omega) hy (Or.inr (Or.inl (by omega))), ?_⟩
    intro hp
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hp
    have hpx := congrArg (fun p => p.1.val) he
    cases l <;> simp only [andCell, andPoint, origin, Bool.toNat_true, Bool.toNat_false] at hpx hx <;> omega
  · intro he
    have hpx := congrArg (fun p => p.1.val) he
    dsimp [point] at hpx
    omega

theorem temporary_floor (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w))) :
    Disjoint (temporaryBoxes w) (andBoard w goals).walls := by
  apply Finset.disjoint_insert_left.mpr
  exact ⟨(normal_row_free w hw goals 4 (by omega) (by omega) (by omega) (by omega)).1,
    (andBoxes_disjoint_walls w hw false true false).mono_left (Finset.erase_subset _ _)⟩

theorem temporary_oldB_free (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w))) :
    Free (andBoard w goals) (temporaryBoxes w) (point w 3 1) := by
  apply free_relocated_of_ne
  · apply and_near_B_free w hw false false goals
    all_goals dsimp [point]; unfold origin; omega
  · intro he
    have hpx := congrArg (fun p => p.1.val) he
    dsimp [point] at hpx
    omega

private theorem temporary_support_free (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w))) :
    Free (andBoard w goals) (temporaryBoxes w) (point w 3 0) := by
  constructor
  · apply and_core_floor w hw
    all_goals dsimp [point]; omega
  · intro hm
    rcases Finset.mem_insert.mp hm with he | he
    · have hpx := congrArg (fun p => p.1.val) he
      dsimp [point] at hpx
      omega
    · exact (Finset.mem_erase.mp he).1 rfl

private theorem closed_A_approach (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w 2 2,andBBoxes w false false true⟩ ⟨point w 2 0,andBBoxes w false false true⟩ := by
  apply walk_vertical (andBBoxes_floor w hw false false goals)
  intro y hy hy'
  apply approach_free w hw goals
  · rfl
  · dsimp [point] at hy' ⊢; omega

private theorem closed_A_push (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w))) :
    Move (andBoard w goals) (some 1) .east
      ⟨point w 2 0,andBBoxes w false false true⟩
      ⟨point w 3 0,insert (point w 4 0) ((andBBoxes w false false true).erase (point w 3 0))⟩ := by
  have hstock := andBBoxes_floor w hw false false goals
  have hsupport : Free (andBoard w goals) (andBBoxes w false false true) (point w 2 0) := by
    apply approach_free w hw goals
    · rfl
    · dsimp [point]; omega
  have hdest : Free (andBoard w goals) (andBBoxes w false false true) (point w 4 0) := by
    apply andBBoxes_free w hw false false goals
    · exact normal_row_free w hw goals 4 (by omega) (by omega) (by omega) (by omega)
    · intro he
      have hpx := congrArg (fun p => p.1.val) he
      dsimp [point] at hpx
      omega
  have hA : point w 3 0 ∈ andBBoxes w false false true := by
    have he : andBCell w false false true .triggerA = point w 3 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [andBCell, andCell, andPoint, point]
    rw [← he]
    exact Finset.mem_image.mpr ⟨.triggerA, Finset.mem_univ _, rfl⟩
  exact Move.single_iff.mpr (SingleMoveView.push ⟨hsupport.1, hstock, hsupport.2⟩
      (by dsimp [Adjacent, point]; omega) hA (by dsimp [Adjacent, point]; omega) hdest.1 hdest.2)

/-- Moving closed A aside is exactly the prepared B stock, retaining every auxiliary box. -/
theorem temporary_prepared (w : ℕ) (hw : 2 ≤ w) :
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

private theorem closed_B_raise (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w))) :
    Move (andBoard w goals) (some 1) .north
      ⟨point w 3 0,insert (point w 4 0) ((andBBoxes w false false true).erase (point w 3 0))⟩
      ⟨point w 3 1,temporaryBoxes w⟩ := by
  have hB : point w 3 2 ∈ temporaryBoxes w := by
    apply Finset.mem_insert_of_mem
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      have hy := congrArg (fun p => p.2.val) he
      dsimp [point] at hy
      unfold origin at hy
      omega
    · exact normal_B_mem w
  rw [temporary_prepared w hw]
  apply restore_move (temporary_floor w hw goals) hB
    (temporary_oldB_free w hw goals) (temporary_support_free w hw goals)
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; unfold origin; omega

private theorem temporary_exit_free (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w))) :
    Free (andBoard w goals) (temporaryBoxes w) (point w 2 1) := by
  apply free_relocated_of_ne
  · apply and_near_B_free w hw false false goals
    all_goals dsimp [point]; unfold origin; omega
  · intro he
    have hx := congrArg (fun p => p.1.val) he
    dsimp [point] at hx
    omega

/-- Move A aside, lift B immediately from the reached support, then exit left. -/
theorem and_B_raise_closedA (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w 2 2, andBBoxes w false false true⟩
      ⟨point w 2 1, temporaryBoxes w⟩ := by
  have hB := closed_B_raise w hw goals
  have hexit := temporary_exit_free w hw goals
  exact (((closed_A_approach w hw goals).tail ⟨.east,closed_A_push w hw goals⟩).tail ⟨.north,hB⟩).tail
    ⟨.west,Move.walk hB.valid_target (by dsimp [Adjacent,point]; omega) hexit.1 hexit.2 rfl⟩

/-- Restore A after lifting B, entering and exiting through the retracted-output mouth. -/
theorem and_B_restore_A (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w (w+4) 1, temporaryBoxes w⟩
      ⟨point w (w+4) 1, andBoxes w false true false⟩ := by
  refine finish_left_via_mouth (andBoxes_disjoint_walls w hw false true false)
    (point w (w+4) 1).1 (point w 5 0).1 (point w 4 0).1 (point w 3 0).1
    (point w (w+4) 1).2 (point w 5 0).2 ?_ ?_ ?_ ?_ ?_ (normal_A_mem w) ?_ ?_ ?_
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [point]; omega
  · exact normal_row_free w hw goals 4 (by omega) (by omega) (by omega) (by omega)
  · apply and_above_free w hw false true false goals
    all_goals dsimp [point]; unfold origin; omega
  · intro x hx hx'
    apply and_row_free w hw false true false goals
    all_goals simp only [point, Bool.toNat_false] at *; omega

/-- Complete the closed-A B update, retaining the explicit exterior connection for restoring A. -/
theorem and_B_forward_closedA (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w)))
    (hconnect : Reachable (andBoard w goals) (some 1)
      ⟨point w 2 1, temporaryBoxes w⟩ ⟨point w (w+4) 1, temporaryBoxes w⟩) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w 2 2, andBoxes w false false false⟩
      ⟨point w (w+4) 1, andBoxes w false true false⟩ :=
  (and_B_tail_forward w hw false false goals).trans
    ((and_B_raise_closedA w hw goals).trans (hconnect.trans (and_B_restore_A w hw goals)))

end PushPuzzle.PushS.FiniteGateBTemporary
