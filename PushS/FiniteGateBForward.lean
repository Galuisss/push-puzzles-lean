/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateBTriggers

/-! Input-side approaches and prepared B-branch completion. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateBForward

open PushFS FiniteGeometry FiniteGateCore FiniteGateMacros FiniteGateVertical
open FiniteGateBTriggers FiniteGateInputs

attribute [local irreducible] side

/-- A relocation preserves each free cell distinct from the newly occupied cell. -/
theorem free_relocated_of_ne {W H : ℕ} {B : Board W H} {stock : Finset (Cell W H)}
    {old next p : Cell W H} (hp : Free B stock p) (hne : p ≠ next) :
    Free B (insert next (stock.erase old)) p := by
  refine ⟨hp.1, ?_⟩
  intro hm
  rcases Finset.mem_insert.mp hm with he | he
  · exact hne he
  · exact hp.2 (Finset.mem_of_mem_erase he)

theorem andBBoxes_free (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) {p : Cell (side w) (side w)}
    (hp : Free (andBoard w goals) (andBoxes w a true c) p)
    (hne : p ≠ point w 3 1) : Free (andBoard w goals) (andBBoxes w a c true) p := by
  rw [← andBBoxes_prepared w hw a c]
  exact free_relocated_of_ne hp hne

theorem andBBoxes_floor (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Disjoint (andBBoxes w a c true) (andBoard w goals).walls := by
  rw [← andBBoxes_prepared w hw a c]
  apply Finset.disjoint_insert_left.mpr
  constructor
  · apply (show Free (andBoard w goals) (andBoxes w a true c) (point w 3 1) from ?_).1
    apply and_near_B_free w hw a c goals
    all_goals dsimp [point]; unfold origin; omega
  · exact (andBoxes_disjoint_walls w hw a true c).mono_left (Finset.erase_subset _ _)

/-- Enter through the retracted-output mouth and walk along the real cavity to B's support. -/
theorem and_B_enter_right (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w (w+4) 1, andBBoxes w true false true⟩
      ⟨point w 3 0, andBBoxes w true false true⟩ := by
  have hrow : ∀ x : Fin (side w), origin w+3 ≤ x.val → x.val ≤ origin w+w+4 →
      Free (andBoard w goals) (andBBoxes w true false true) (x, (point w 3 0).2) := by
    intro x hx hx'
    apply andBBoxes_free w hw true false goals
    · apply and_row_free w hw true true false goals
      all_goals simp only [point, Bool.toNat_true, Bool.toNat_false]
      all_goals have ha := Bool.toNat_le true; omega
    · intro he
      have hy := congrArg (fun p => p.2.val) he
      dsimp [point] at hy
      unfold origin at hy
      omega
  have hupper : Free (andBoard w goals) (andBBoxes w true false true) (point w (w+4) 1) := by
    apply andBBoxes_free w hw true false goals
    · apply and_above_free w hw true true false goals
      all_goals dsimp [point]; unfold origin; omega
    · intro he
      have hx := congrArg (fun p => p.1.val) he
      dsimp [point] at hx
      omega
  have hfree := hrow (point w (w+4) 0).1 (by dsimp [point]; omega) (by dsimp [point]; omega)
  have hdown : SingleMoveView (andBoard w goals) .south
      (⟨point w (w+4) 1, andBBoxes w true false true⟩ : State (side w) (side w))
      ⟨point w (w+4) 0, andBBoxes w true false true⟩ :=
    SingleMoveView.walk ⟨hupper.1, andBBoxes_floor w hw true false goals, hupper.2⟩
      (by dsimp [Adjacent, point]; unfold origin; omega) hfree.1 hfree.2
  have hwalk := walk_horizontal (andBBoxes_floor w hw true false goals)
    (point w (w+4) 0).1 (point w 3 0).1 (point w 3 0).2 (by
      intro x hx hx'
      apply hrow x <;> dsimp [point] at * <;> omega)
  exact (Relation.ReflTransGen.single ⟨.south, Move.single_iff.mpr hdown⟩).trans hwalk

theorem orBBoxes_free (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) {p : Cell (side w) (side w)}
    (hp : Free (orBoard w goals) (orBoxes w a true c) p)
    (hne : p ≠ point w 4 1) : Free (orBoard w goals) (orBBoxes w a c true) p := by
  rw [← orBBoxes_prepared w hw a c]
  exact free_relocated_of_ne hp hne

theorem orBBoxes_floor (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Disjoint (orBBoxes w a c true) (orBoard w goals).walls := by
  rw [← orBBoxes_prepared w hw a c]
  apply Finset.disjoint_insert_left.mpr
  constructor
  · apply (show Free (orBoard w goals) (orBoxes w a true c) (point w 4 1) from ?_).1
    apply or_near_B_free w hw a c goals
    all_goals dsimp [point]; unfold origin; omega
  · exact (orBoxes_disjoint_walls w hw a true c).mono_left (Finset.erase_subset _ _)

/-- Enter through the retracted-output mouth and walk along the real cavity to B's support. -/
theorem or_B_enter_right (w : ℕ) (hw : 2 ≤ w) (a : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w (w+5) 1, orBBoxes w a false true⟩
      ⟨point w 4 0, orBBoxes w a false true⟩ := by
  have hrow : ∀ x : Fin (side w), origin w+4 ≤ x.val → x.val ≤ origin w+w+5 →
      Free (orBoard w goals) (orBBoxes w a false true) (x, (point w 4 0).2) := by
    intro x hx hx'
    apply orBBoxes_free w hw a false goals
    · apply or_row_free w hw a true false goals
      all_goals simp only [point, Bool.toNat_false]
      all_goals have ha := Bool.toNat_le a; omega
    · intro he
      have hy := congrArg (fun p => p.2.val) he
      dsimp [point] at hy
      unfold origin at hy
      omega
  have hupper : Free (orBoard w goals) (orBBoxes w a false true) (point w (w+5) 1) := by
    apply orBBoxes_free w hw a false goals
    · apply or_above_free w hw a true false goals
      all_goals dsimp [point]; unfold origin; omega
    · intro he
      have hx := congrArg (fun p => p.1.val) he
      dsimp [point] at hx
      omega
  have hfree := hrow (point w (w+5) 0).1 (by dsimp [point]; omega) (by dsimp [point]; omega)
  have hdown : SingleMoveView (orBoard w goals) .south
      (⟨point w (w+5) 1, orBBoxes w a false true⟩ : State (side w) (side w))
      ⟨point w (w+5) 0, orBBoxes w a false true⟩ :=
    SingleMoveView.walk ⟨hupper.1, orBBoxes_floor w hw a false goals, hupper.2⟩
      (by dsimp [Adjacent, point]; unfold origin; omega) hfree.1 hfree.2
  have hwalk := walk_horizontal (orBBoxes_floor w hw a false goals)
    (point w (w+5) 0).1 (point w 4 0).1 (point w 4 0).2 (by
      intro x hx hx'
      apply hrow x <;> dsimp [point] at * <;> omega)
  exact (Relation.ReflTransGen.single ⟨.south, Move.single_iff.mpr hdown⟩).trans hwalk

private theorem or_approach_A_free (w : ℕ) (hw : 2 ≤ w) (c : Bool)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hx : p.1.val = origin w+3) (hy : p.2.val ≤ origin w) :
    Free (orBoard w goals) (orBBoxes w true c true) p := by
  apply orBBoxes_free w hw true c goals
  · refine ⟨or_core_floor w hw p (by omega) hy (Or.inr (Or.inl (by omega))), ?_⟩
    intro hp
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hp
    have hpx := congrArg (fun p => p.1.val) he
    have hc := Bool.toNat_le c
    cases l <;> simp only [orCell, orPoint, origin, Bool.toNat_true] at hpx hx <;> omega
  · intro he
    have hpx := congrArg (fun p => p.1.val) he
    dsimp [point] at hpx
    omega

/-- An open A gives an explicit left approach to B, even with the output contracted. -/
theorem or_B_enter_left (w : ℕ) (hw : 2 ≤ w) (c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 3 2, orBBoxes w true c true⟩ ⟨point w 4 0, orBBoxes w true c true⟩ := by
  have hstock := orBBoxes_floor w hw true c goals
  have hstart : Free (orBoard w goals) (orBBoxes w true c true) (point w 3 2) := by
    apply or_approach_A_free w hw c goals
    · rfl
    · dsimp [point]; omega
  have hwalk := walk_vertical hstock (point w 3 2).1 (point w 3 2).2 (point w 3 0).2 (by
    intro y hy hy'
    apply or_approach_A_free w hw c goals
    · rfl
    · dsimp [point] at hy' ⊢; omega)
  have hsupport : Free (orBoard w goals) (orBBoxes w true c true) (point w 4 0) := by
    apply orBBoxes_free w hw true c goals
    · apply or_row_free w hw true true c goals
      all_goals simp only [point, Bool.toNat_true]; have hc := Bool.toNat_le c; omega
    · intro he
      have hpy := congrArg (fun p => p.2.val) he
      dsimp [point] at hpy
      unfold origin at hpy
      omega
  exact hwalk.tail ⟨.east, Move.walk
    (hwalk.valid ⟨hstart.1, hstock, hstart.2⟩) (by dsimp [Adjacent, point]; omega)
    hsupport.1 hsupport.2 rfl⟩

/-- Update the complete OR B branch through the open A entrance. -/
theorem or_B_forward_A (w : ℕ) (hw : 2 ≤ w) (c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 3 2, orBoxes w true false c⟩ ⟨point w 3 1, orBoxes w true true c⟩ :=
  (or_B_tail_forward w hw true c goals).trans
    ((or_B_enter_left w hw c goals).trans (or_B_up w hw true c goals))

/-- Update the complete AND B branch through its explicit output-side entrance connection. -/
theorem and_B_forward_openA (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w)))
    (hconnect : Reachable (andBoard w goals) (some 1)
      ⟨point w 2 2, andBBoxes w true false true⟩
      ⟨point w (w+4) 1, andBBoxes w true false true⟩) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w 2 2, andBoxes w true false false⟩
      ⟨point w 2 1, andBoxes w true true false⟩ :=
  (and_B_tail_forward w hw true false goals).trans
    (hconnect.trans ((and_B_enter_right w hw goals).trans (and_B_up w hw false goals)))

/-- Update the complete OR B branch with its explicit output-side entrance connection. -/
theorem or_B_forward_right (w : ℕ) (hw : 2 ≤ w) (a : Bool)
    (goals : Finset (Cell (side w) (side w)))
    (hconnect : Reachable (orBoard w goals) (some 1)
      ⟨point w 3 2, orBBoxes w a false true⟩
      ⟨point w (w+5) 1, orBBoxes w a false true⟩) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 3 2, orBoxes w a false false⟩
      ⟨point w 3 1, orBoxes w a true false⟩ :=
  (or_B_tail_forward w hw a false goals).trans
    (hconnect.trans ((or_B_enter_right w hw a goals).trans (or_B_up w hw a false goals)))

end PushPuzzle.PushS.FiniteGateBForward
