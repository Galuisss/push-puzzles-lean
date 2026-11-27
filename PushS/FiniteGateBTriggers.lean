/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateVertical
public import PushS.FiniteGateOutputReturn

/-! Real B-trigger updates and complete reverse B-branch propagation. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateBTriggers

open PushFS FiniteGeometry FiniteGateCore FiniteGateMacros FiniteGatePrepared
open FiniteGateVertical FiniteGateInputs FiniteVerticalLineMacros

attribute [local irreducible] side

/-- Push a prepared box into its missing normal slot, restoring the exact target inventory. -/
theorem restore_move {W H : ℕ} {B : Board W H} {target : Finset (Cell W H)}
    {support old next : Cell W H} {d : Direction}
    (hboxes : Disjoint target B.walls) (hnext : next ∈ target)
    (hold : Free B target old) (hsupport : Free B target support)
    (hax : Adjacent d support old) (hxn : Adjacent d old next) :
    Move B (some 1) d ⟨support, insert old (target.erase next)⟩ ⟨old, target⟩ := by
  have hprepared : Disjoint (insert old (target.erase next)) B.walls :=
    Finset.disjoint_insert_left.mpr ⟨hold.1, hboxes.mono_left (Finset.erase_subset _ _)⟩
  have hsupport' : support ∉ insert old (target.erase next) := by
    intro hm
    rcases Finset.mem_insert.mp hm with he | he
    · exact hax.ne he
    · exact hsupport.2 (Finset.mem_of_mem_erase he)
  have hnext' : next ∉ insert old (target.erase next) := by
    intro hm
    rcases Finset.mem_insert.mp hm with he | he
    · exact hxn.ne he.symm
    · exact (Finset.mem_erase.mp he).1 rfl
  have heq : insert next ((insert old (target.erase next)).erase old) = target := by
    rw [Finset.erase_insert (fun hm => hold.2 (Finset.mem_of_mem_erase hm))]
    exact Finset.insert_erase hnext
  have hm := SingleMoveView.push (s := (⟨support, insert old (target.erase next)⟩ : State W H))
    ⟨hsupport.1, hprepared, hsupport'⟩ hax (Finset.mem_insert_self _ _) hxn
    (fun hw => Finset.disjoint_left.mp hboxes hnext hw) hnext'
  exact Move.single_iff.mpr (by simpa only [heq] using hm)

/-- Free cells in the three-row B neighborhood, with its occupied normal slot excluded. -/
theorem and_near_B_free (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hx : origin w+2 ≤ p.1.val) (hx' : p.1.val ≤ origin w+3)
    (hy : p.2.val+1 ≤ origin w) (hy' : origin w ≤ p.2.val+3)
    (hB : p.1.val ≠ origin w+3 ∨ p.2.val+2 ≠ origin w) :
    Free (andBoard w goals) (andBoxes w a true c) p := by
  refine ⟨and_core_floor w hw p (by omega) (by omega) (Or.inr (Or.inl hx')), ?_⟩
  intro hp
  obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hp
  have hpx := congrArg (fun p => p.1.val) he
  have hpy := congrArg (fun p => p.2.val) he
  have ha := Bool.toNat_le a
  have hc := Bool.toNat_le c
  cases l <;> simp only [andCell, andPoint, origin, Bool.toNat_true] at hpx hpy hx hx' hy hy' hB <;> omega

/-- Release B downward while its upper-tail boxes remain in their normal new slots. -/
theorem and_B_down (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w 2 2, andBoxes w a true c⟩
      ⟨point w 2 2, andBBoxes w a c true⟩ := by
  rw [← andBBoxes_prepared w hw a c]
  have hsource : point w 3 2 ∈ andBoxes w a true c := by
    have he : andCell w a true c (.branchB 0) = point w 3 2 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]; omega
    rw [← he]
    exact Finset.mem_image.mpr ⟨.branchB 0, Finset.mem_univ _, rfl⟩
  refine push_via_parallel_column (andBoxes_disjoint_walls w hw a true c)
    (point w 2 2).2 (point w 3 3).2 (point w 3 2).2 (point w 3 1).2
    (point w 2 2).1 (point w 3 2).1 .east .south ?_ ?_ ?_ ?_ ?_ hsource ?_ ?_ ?_
  · dsimp [Adjacent, point]; omega
  · dsimp [Adjacent, Direction.opposite, point]; omega
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; unfold origin; omega
  · apply and_near_B_free w hw a c goals
    all_goals dsimp [point]; unfold origin; omega
  · apply and_near_B_free w hw a c goals
    all_goals dsimp [point]; unfold origin; omega
  · intro y hy hy'
    apply and_near_B_free w hw a c goals
    all_goals dsimp [point] at *; unfold origin at *; omega
  · intro y hy hy'
    apply and_near_B_free w hw a c goals
    all_goals dsimp [point] at *; unfold origin at *; omega

/-- Release B and update every upper-tail box back to the complete old normal state. -/
theorem and_B_backward (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w 2 2, andBoxes w a true c⟩
      ⟨point w 2 2, andBoxes w a false c⟩ :=
  (and_B_down w hw a c goals).trans (and_B_tail_backward w hw a c goals)

/-- Free cells in the three-row B neighborhood, with its occupied normal slot excluded. -/
theorem or_near_B_free (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hx : origin w+3 ≤ p.1.val) (hx' : p.1.val ≤ origin w+4)
    (hy : p.2.val+1 ≤ origin w) (hy' : origin w ≤ p.2.val+3)
    (hB : p.1.val ≠ origin w+4 ∨ p.2.val+2 ≠ origin w) :
    Free (orBoard w goals) (orBoxes w a true c) p := by
  refine ⟨or_core_floor w hw p (by omega) (by omega) (Or.inr (Or.inl hx')), ?_⟩
  intro hp
  obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hp
  have hpx := congrArg (fun p => p.1.val) he
  have hpy := congrArg (fun p => p.2.val) he
  have ha := Bool.toNat_le a
  have hc := Bool.toNat_le c
  cases l <;> simp only [orCell, orPoint, origin, Bool.toNat_true] at hpx hpy hx hx' hy hy' hB <;> omega

/-- Release B downward while its upper-tail boxes remain in their normal new slots. -/
theorem or_B_down (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 3 2, orBoxes w a true c⟩
      ⟨point w 3 2, orBBoxes w a c true⟩ := by
  rw [← orBBoxes_prepared w hw a c]
  have hsource : point w 4 2 ∈ orBoxes w a true c := by
    have he : orCell w a true c (.branchB 0) = point w 4 2 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]; omega
    rw [← he]
    exact Finset.mem_image.mpr ⟨.branchB 0, Finset.mem_univ _, rfl⟩
  refine push_via_parallel_column (orBoxes_disjoint_walls w hw a true c)
    (point w 3 2).2 (point w 4 3).2 (point w 4 2).2 (point w 4 1).2
    (point w 3 2).1 (point w 4 2).1 .east .south ?_ ?_ ?_ ?_ ?_ hsource ?_ ?_ ?_
  · dsimp [Adjacent, point]; omega
  · dsimp [Adjacent, Direction.opposite, point]; omega
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; unfold origin; omega
  · apply or_near_B_free w hw a c goals
    all_goals dsimp [point]; unfold origin; omega
  · apply or_near_B_free w hw a c goals
    all_goals dsimp [point]; unfold origin; omega
  · intro y hy hy'
    apply or_near_B_free w hw a c goals
    all_goals dsimp [point] at *; unfold origin at *; omega
  · intro y hy hy'
    apply or_near_B_free w hw a c goals
    all_goals dsimp [point] at *; unfold origin at *; omega

/-- Release B and update every upper-tail box back to the complete old normal state. -/
theorem or_B_backward (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 3 2, orBoxes w a true c⟩
      ⟨point w 3 2, orBoxes w a false c⟩ :=
  (or_B_down w hw a c goals).trans (or_B_tail_backward w hw a c goals)

/-- Lift the prepared B trigger from its actual row support and exit to its left. -/
theorem and_B_up (w : ℕ) (hw : 2 ≤ w) (c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w 3 0, andBBoxes w true c true⟩
      ⟨point w 2 1, andBoxes w true true c⟩ := by
  have hnext : point w 3 2 ∈ andBoxes w true true c := by
    have he : andCell w true true c (.branchB 0) = point w 3 2 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]; omega
    rw [← he]
    exact Finset.mem_image.mpr ⟨.branchB 0, Finset.mem_univ _, rfl⟩
  have hpush : Move (andBoard w goals) (some 1) .north
      ⟨point w 3 0, andBBoxes w true c true⟩
      ⟨point w 3 1, andBoxes w true true c⟩ := by
    rw [← andBBoxes_prepared w hw true c]
    apply restore_move (andBoxes_disjoint_walls w hw true true c) hnext
    · apply and_near_B_free w hw true c goals
      all_goals dsimp [point]; unfold origin; omega
    · apply and_row_free w hw true true c goals
      all_goals simp only [point, Bool.toNat_true]
      all_goals have hc := Bool.toNat_le c; have ha := Bool.toNat_le true; omega
    · dsimp [Adjacent, point]; unfold origin; omega
    · dsimp [Adjacent, point]; unfold origin; omega
  have hfree : Free (andBoard w goals) (andBoxes w true true c) (point w 2 1) := by
    apply and_near_B_free w hw true c goals
    all_goals dsimp [point]; unfold origin; omega
  exact (Relation.ReflTransGen.single ⟨.north, hpush⟩).tail
    ⟨.west, Move.walk hpush.valid_target (by dsimp [Adjacent, point]; omega) hfree.1 hfree.2 rfl⟩

/-- Lift the prepared B trigger from its actual row support and exit to its left. -/
theorem or_B_up (w : ℕ) (hw : 2 ≤ w) (a : Bool) (c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 4 0, orBBoxes w a c true⟩
      ⟨point w 3 1, orBoxes w a true c⟩ := by
  have hnext : point w 4 2 ∈ orBoxes w a true c := by
    have he : orCell w a true c (.branchB 0) = point w 4 2 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]; omega
    rw [← he]
    exact Finset.mem_image.mpr ⟨.branchB 0, Finset.mem_univ _, rfl⟩
  have hpush : Move (orBoard w goals) (some 1) .north
      ⟨point w 4 0, orBBoxes w a c true⟩
      ⟨point w 4 1, orBoxes w a true c⟩ := by
    rw [← orBBoxes_prepared w hw a c]
    apply restore_move (orBoxes_disjoint_walls w hw a true c) hnext
    · apply or_near_B_free w hw a c goals
      all_goals dsimp [point]; unfold origin; omega
    · apply or_row_free w hw a true c goals
      all_goals simp only [point]
      all_goals have hc := Bool.toNat_le c; have ha := Bool.toNat_le a; omega
    · dsimp [Adjacent, point]; unfold origin; omega
    · dsimp [Adjacent, point]; unfold origin; omega
  have hfree : Free (orBoard w goals) (orBoxes w a true c) (point w 3 1) := by
    apply or_near_B_free w hw a c goals
    all_goals dsimp [point]; unfold origin; omega
  exact (Relation.ReflTransGen.single ⟨.north, hpush⟩).tail
    ⟨.west, Move.walk hpush.valid_target (by dsimp [Adjacent, point]; omega) hfree.1 hfree.2 rfl⟩

end PushPuzzle.PushS.FiniteGateBTriggers
