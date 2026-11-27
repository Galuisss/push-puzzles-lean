/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateInputs
public import PushS.FiniteGateState
public import PushS.FiniteVerticalLineMacros
import Mathlib.Tactic.FinCases

/-! Complete B-tail sweeps with the first trigger held in its prepared old slot. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateVertical

open PushFS FiniteGeometry FiniteGateCore FiniteGateMacros FiniteLineMacros
open FiniteVerticalLineMacros

attribute [local irreducible] side

/-- The vertical input tail is a horizontal gap-two line in transposed coordinates. -/
def inputBLine (w n column : ℕ) (hn : n ≤ 4*w+15 := by omega)
    (hc : 1 ≤ column ∧ column ≤ 4 := by omega) : Line (side w) (side w) where
  count := n
  base := origin w-2*n-2
  base_pos := by unfold origin; omega
  fits := by unfold origin side; omega
  row := (point w column 0).1
  lane := (point w (column-1) 0).1
  entry := .south
  crossing := by intro x; dsimp [Adjacent, point]; omega
  hub := (point w 0 2).2

private def reverseBIndex (n : ℕ) (i : Fin n) : Fin (n+1) :=
  ⟨n-i.val, by have := i.isLt; omega⟩

def andBKeep {w : ℕ} : AndLabel w → Bool
  | .branchB i => decide (i = 0)
  | _ => true

def andBFixed (w : ℕ) (a c : Bool) : Finset (Cell (side w) (side w)) :=
  (Finset.univ.filter fun l => andBKeep l).image (andCell w a false c)

/-- The upper tail has phase `q`; its first B trigger retains the old slot. -/
def andBCell (w : ℕ) (a c q : Bool) (l : AndLabel w) : Cell (side w) (side w) :=
  match l with
  | .branchB i => andCell w a (if i = 0 then false else q) c l
  | _ => andCell w a false c l

def andBBoxes (w : ℕ) (a c q : Bool) : Finset (Cell (side w) (side w)) :=
  Finset.univ.image (andBCell w a c q)

private theorem andBCell_kept (w : ℕ) (a c q : Bool) (l : AndLabel w)
    (hl : andBKeep l = true) : andBCell w a c q l = andCell w a false c l := by
  cases l <;> try rfl
  rename_i i
  have hi : i = 0 := by simpa only [andBKeep, decide_eq_true_eq] using hl
  subst i
  rfl

private theorem andBFixed_free (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hx : origin w+2 ≤ p.1.val) (hx' : p.1.val ≤ origin w+3)
    (hy : p.2.val+2 ≤ origin w) :
    Free (andBoard w goals) (andBFixed w a c) p := by
  constructor
  · intro hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    have hi' := ((andRectangle w i).mem_cells _ _ _).mp hi
    fin_cases i <;> simp [andRectangle, origin] at hi' hx hx' hy <;> omega
  · intro hp
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hp
    have hkeep := (Finset.mem_filter.mp hl).2
    have hpx := congrArg (fun p => p.1.val) he
    have hpy := congrArg (fun p => p.2.val) he
    have ha := Bool.toNat_le a
    have hc := Bool.toNat_le c
    cases l <;> simp only [andCell, andPoint, origin, Bool.toNat_false] at hpx hpy hx hx' hy
    all_goals try omega
    rename_i i
    have hi : i = 0 := by simpa only [andBKeep, decide_eq_true_eq] using hkeep
    subst i
    simp only [Fin.val_zero] at hpy
    omega

/-- The entire upper tail uses the exposed column to the left of B. -/
theorem andBFrame (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    FiniteVerticalLineMacros.Frame (inputBLine w (4*w+15) 3) (andBoard w goals) (andBFixed w a c) := by
  constructor
  · apply (andBoxes_disjoint_walls w hw a false c).mono_left
    intro p hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩
  · intro y hy
    apply andBFixed_free w hw a c goals
    all_goals dsimp [inputBLine, Line.track, point] at *; unfold origin at *; omega
  · intro y hy
    apply andBFixed_free w hw a c goals
    all_goals dsimp [inputBLine, Line.laneSegment, point] at *; unfold origin at *; omega

private theorem andBLine_position (w : ℕ) (a c q : Bool) (i : Fin (4*w+15)) :
    Prod.swap ((inputBLine w (4*w+15) 3).position (if q then 4*w+15 else 0) i) =
      andBCell w a c q (.branchB (reverseBIndex (4*w+15) i)) := by
  have hi : reverseBIndex (4*w+15) i ≠ 0 := by
    intro he
    have he' := congrArg Fin.val he
    simp only [reverseBIndex, Fin.val_zero] at he'
    have := i.isLt
    omega
  simp only [andBCell, hi, ite_false]
  have hbound := i.isLt
  cases q <;> apply Prod.ext <;> apply Fin.ext <;>
    simp [inputBLine, Line.position, point, andCell, andPoint,
      reverseBIndex, Prod.swap, hbound, origin]
  all_goals omega

theorem andBLine_boxes (w : ℕ) (a c q : Bool) :
    FiniteVerticalLineMacros.boxes (inputBLine w (4*w+15) 3) (andBFixed w a c)
      (if q then 4*w+15 else 0) = andBBoxes w a c q := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _,
        andBCell_kept w a c q l (Finset.mem_filter.mp hl).2⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨.branchB (reverseBIndex (4*w+15) i), Finset.mem_univ _,
        (andBLine_position w a c q i).symm⟩
  · intro hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    by_cases hkeep : andBKeep l = true
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkeep⟩,
        (andBCell_kept w a c q l hkeep).symm⟩
    · cases l <;> try exact False.elim (hkeep rfl)
      rename_i i
      have hi : i ≠ 0 := by
        intro he
        subst i
        exact hkeep rfl
      have hival := Fin.val_ne_of_ne hi
      simp only [Fin.val_zero] at hival
      let j : Fin (4*w+15) := ⟨(4*w+15)-i.val, by have := i.isLt; omega⟩
      have hj : reverseBIndex (4*w+15) j = i := by
        apply Fin.ext
        have := i.isLt
        dsimp [j, reverseBIndex]
        omega
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by
        rw [andBLine_position, hj]⟩

theorem andBBoxes_false (w : ℕ) (a c : Bool) : andBBoxes w a c false = andBoxes w a false c := by
  unfold andBBoxes andBoxes
  congr 1
  funext l
  cases l <;> simp [andBCell]

/-- The updated upper tail leaves B in its old slot as the prepared final trigger. -/
theorem andBBoxes_prepared (w : ℕ) (hw : 2 ≤ w) (a c : Bool) :
    insert (point w 3 1) ((andBoxes w a true c).erase (point w 3 2)) =
      andBBoxes w a c true := by
  have he := Line.image_relocate (andCell w a true c) (andBCell w a c true)
    (andCell_injective w hw a true c) (.branchB 0) (by
      intro l hl
      cases l <;> try rfl
      rename_i i
      have hi : i ≠ 0 := fun h => hl (by rw [h])
      simp only [andBCell, hi, ite_false])
  have hold : andBCell w a c true (.branchB 0) = point w 3 1 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [andBCell, andCell, andPoint, point]
  have hnew : andCell w a true c (.branchB 0) = point w 3 2 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]; omega
  simpa only [andBoxes, andBBoxes, hold, hnew] using he

/-- Propagate every upper-tail box toward the prepared B trigger. -/
theorem and_B_tail_forward (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w 2 2, andBoxes w a false c⟩
      ⟨point w 2 2, andBBoxes w a c true⟩ := by
  have hr := (andBFrame w hw a c goals).forward
  have hzero := andBLine_boxes w a c false
  change FiniteVerticalLineMacros.boxes (inputBLine w (4*w+15) 3) (andBFixed w a c) 0 =
    andBBoxes w a c false at hzero
  have hfull := andBLine_boxes w a c true
  change FiniteVerticalLineMacros.boxes (inputBLine w (4*w+15) 3) (andBFixed w a c) (4*w+15) =
    andBBoxes w a c true at hfull
  change Reachable (andBoard w goals) (some 1)
    ⟨point w 2 2, FiniteVerticalLineMacros.boxes (inputBLine w (4*w+15) 3) (andBFixed w a c) 0⟩
    ⟨point w 2 2, FiniteVerticalLineMacros.boxes (inputBLine w (4*w+15) 3) (andBFixed w a c) (4*w+15)⟩ at hr
  rw [hzero, hfull, andBBoxes_false] at hr
  exact hr

/-- Propagate every upper-tail box back after the B trigger has been released. -/
theorem and_B_tail_backward (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w 2 2, andBBoxes w a c true⟩
      ⟨point w 2 2, andBoxes w a false c⟩ := by
  have hr := (andBFrame w hw a c goals).backward
  have hzero := andBLine_boxes w a c false
  change FiniteVerticalLineMacros.boxes (inputBLine w (4*w+15) 3) (andBFixed w a c) 0 =
    andBBoxes w a c false at hzero
  have hfull := andBLine_boxes w a c true
  change FiniteVerticalLineMacros.boxes (inputBLine w (4*w+15) 3) (andBFixed w a c) (4*w+15) =
    andBBoxes w a c true at hfull
  change Reachable (andBoard w goals) (some 1)
    ⟨point w 2 2, FiniteVerticalLineMacros.boxes (inputBLine w (4*w+15) 3) (andBFixed w a c) (4*w+15)⟩
    ⟨point w 2 2, FiniteVerticalLineMacros.boxes (inputBLine w (4*w+15) 3) (andBFixed w a c) 0⟩ at hr
  rw [hfull, hzero, andBBoxes_false] at hr
  exact hr

def orBKeep {w : ℕ} : OrLabel w → Bool
  | .branchB i => decide (i = 0)
  | _ => true

def orBFixed (w : ℕ) (a c : Bool) : Finset (Cell (side w) (side w)) :=
  (Finset.univ.filter fun l => orBKeep l).image (orCell w a false c)

/-- The upper tail has phase `q`; its first B trigger retains the old slot. -/
def orBCell (w : ℕ) (a c q : Bool) (l : OrLabel w) : Cell (side w) (side w) :=
  match l with
  | .branchB i => orCell w a (if i = 0 then false else q) c l
  | _ => orCell w a false c l

def orBBoxes (w : ℕ) (a c q : Bool) : Finset (Cell (side w) (side w)) :=
  Finset.univ.image (orBCell w a c q)

private theorem orBCell_kept (w : ℕ) (a c q : Bool) (l : OrLabel w)
    (hl : orBKeep l = true) : orBCell w a c q l = orCell w a false c l := by
  cases l <;> try rfl
  rename_i i
  have hi : i = 0 := by simpa only [orBKeep, decide_eq_true_eq] using hl
  subst i
  rfl

private theorem orBFixed_free (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hx : origin w+3 ≤ p.1.val) (hx' : p.1.val ≤ origin w+4)
    (hy : p.2.val+2 ≤ origin w) :
    Free (orBoard w goals) (orBFixed w a c) p := by
  constructor
  · intro hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    have hi' := ((orRectangle w i).mem_cells _ _ _).mp hi
    fin_cases i <;> simp [orRectangle, origin] at hi' hx hx' hy <;> omega
  · intro hp
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hp
    have hkeep := (Finset.mem_filter.mp hl).2
    have hpx := congrArg (fun p => p.1.val) he
    have hpy := congrArg (fun p => p.2.val) he
    have ha := Bool.toNat_le a
    have hc := Bool.toNat_le c
    cases l <;> simp only [orCell, orPoint, origin, Bool.toNat_false] at hpx hpy hx hx' hy
    all_goals try omega
    rename_i i
    have hi : i = 0 := by simpa only [orBKeep, decide_eq_true_eq] using hkeep
    subst i
    simp only [Fin.val_zero] at hpy
    omega

/-- The entire upper tail uses the exposed column to the left of B. -/
theorem orBFrame (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    FiniteVerticalLineMacros.Frame (inputBLine w (w+6) 4) (orBoard w goals) (orBFixed w a c) := by
  constructor
  · apply (orBoxes_disjoint_walls w hw a false c).mono_left
    intro p hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩
  · intro y hy
    apply orBFixed_free w hw a c goals
    all_goals dsimp [inputBLine, Line.track, point] at *; unfold origin at *; omega
  · intro y hy
    apply orBFixed_free w hw a c goals
    all_goals dsimp [inputBLine, Line.laneSegment, point] at *; unfold origin at *; omega

private theorem orBLine_position (w : ℕ) (a c q : Bool) (i : Fin (w+6)) :
    Prod.swap ((inputBLine w (w+6) 4).position (if q then w+6 else 0) i) =
      orBCell w a c q (.branchB (reverseBIndex (w+6) i)) := by
  have hi : reverseBIndex (w+6) i ≠ 0 := by
    intro he
    have he' := congrArg Fin.val he
    simp only [reverseBIndex, Fin.val_zero] at he'
    have := i.isLt
    omega
  simp only [orBCell, hi, ite_false]
  have hbound := i.isLt
  cases q <;> apply Prod.ext <;> apply Fin.ext <;>
    simp [inputBLine, Line.position, point, orCell, orPoint,
      reverseBIndex, Prod.swap, hbound, origin]
  all_goals omega

theorem orBLine_boxes (w : ℕ) (a c q : Bool) :
    FiniteVerticalLineMacros.boxes (inputBLine w (w+6) 4) (orBFixed w a c)
      (if q then w+6 else 0) = orBBoxes w a c q := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _,
        orBCell_kept w a c q l (Finset.mem_filter.mp hl).2⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨.branchB (reverseBIndex (w+6) i), Finset.mem_univ _,
        (orBLine_position w a c q i).symm⟩
  · intro hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    by_cases hkeep : orBKeep l = true
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkeep⟩,
        (orBCell_kept w a c q l hkeep).symm⟩
    · cases l <;> try exact False.elim (hkeep rfl)
      rename_i i
      have hi : i ≠ 0 := by
        intro he
        subst i
        exact hkeep rfl
      have hival := Fin.val_ne_of_ne hi
      simp only [Fin.val_zero] at hival
      let j : Fin (w+6) := ⟨(w+6)-i.val, by have := i.isLt; omega⟩
      have hj : reverseBIndex (w+6) j = i := by
        apply Fin.ext
        have := i.isLt
        dsimp [j, reverseBIndex]
        omega
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by
        rw [orBLine_position, hj]⟩

theorem orBBoxes_false (w : ℕ) (a c : Bool) : orBBoxes w a c false = orBoxes w a false c := by
  unfold orBBoxes orBoxes
  congr 1
  funext l
  cases l <;> simp [orBCell]

/-- The updated upper tail leaves B in its old slot as the prepared final trigger. -/
theorem orBBoxes_prepared (w : ℕ) (hw : 2 ≤ w) (a c : Bool) :
    insert (point w 4 1) ((orBoxes w a true c).erase (point w 4 2)) =
      orBBoxes w a c true := by
  have he := Line.image_relocate (orCell w a true c) (orBCell w a c true)
    (orCell_injective w hw a true c) (.branchB 0) (by
      intro l hl
      cases l <;> try rfl
      rename_i i
      have hi : i ≠ 0 := fun h => hl (by rw [h])
      simp only [orBCell, hi, ite_false])
  have hold : orBCell w a c true (.branchB 0) = point w 4 1 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [orBCell, orCell, orPoint, point]
  have hnew : orCell w a true c (.branchB 0) = point w 4 2 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]; omega
  simpa only [orBoxes, orBBoxes, hold, hnew] using he

/-- Propagate every upper-tail box toward the prepared B trigger. -/
theorem or_B_tail_forward (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 3 2, orBoxes w a false c⟩
      ⟨point w 3 2, orBBoxes w a c true⟩ := by
  have hr := (orBFrame w hw a c goals).forward
  have hzero := orBLine_boxes w a c false
  change FiniteVerticalLineMacros.boxes (inputBLine w (w+6) 4) (orBFixed w a c) 0 =
    orBBoxes w a c false at hzero
  have hfull := orBLine_boxes w a c true
  change FiniteVerticalLineMacros.boxes (inputBLine w (w+6) 4) (orBFixed w a c) (w+6) =
    orBBoxes w a c true at hfull
  change Reachable (orBoard w goals) (some 1)
    ⟨point w 3 2, FiniteVerticalLineMacros.boxes (inputBLine w (w+6) 4) (orBFixed w a c) 0⟩
    ⟨point w 3 2, FiniteVerticalLineMacros.boxes (inputBLine w (w+6) 4) (orBFixed w a c) (w+6)⟩ at hr
  rw [hzero, hfull, orBBoxes_false] at hr
  exact hr

/-- Propagate every upper-tail box back after the B trigger has been released. -/
theorem or_B_tail_backward (w : ℕ) (hw : 2 ≤ w) (a c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 3 2, orBBoxes w a c true⟩
      ⟨point w 3 2, orBoxes w a false c⟩ := by
  have hr := (orBFrame w hw a c goals).backward
  have hzero := orBLine_boxes w a c false
  change FiniteVerticalLineMacros.boxes (inputBLine w (w+6) 4) (orBFixed w a c) 0 =
    orBBoxes w a c false at hzero
  have hfull := orBLine_boxes w a c true
  change FiniteVerticalLineMacros.boxes (inputBLine w (w+6) 4) (orBFixed w a c) (w+6) =
    orBBoxes w a c true at hfull
  change Reachable (orBoard w goals) (some 1)
    ⟨point w 3 2, FiniteVerticalLineMacros.boxes (inputBLine w (w+6) 4) (orBFixed w a c) (w+6)⟩
    ⟨point w 3 2, FiniteVerticalLineMacros.boxes (inputBLine w (w+6) 4) (orBFixed w a c) 0⟩ at hr
  rw [hfull, hzero, orBBoxes_false] at hr
  exact hr

end PushPuzzle.PushS.FiniteGateVertical
