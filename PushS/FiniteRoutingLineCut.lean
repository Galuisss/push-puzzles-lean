/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineBoard
public import PushS.FiniteWireFrame
public import Mathlib.Data.List.Forall2

/-! Physical-label propagation cuts preserve the first interface and exact shared endpoint ownership. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line

open PushFS

private theorem Atom.positions_low_high (w : ℕ) (a : Atom) :
    List.Forall₂ (· ≤ ·) (a.positions w false) (a.positions w true) := by
  cases a with
  | line n =>
    simp only [Atom.positions, Bool.toNat_false, Bool.toNat_true,
      List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro i _
    omega
  | flip => simp [Atom.positions]
  | parity => simp [Atom.positions]

private theorem positions_low_high (w : ℕ) (atoms : List Atom) :
    List.Forall₂ (· ≤ ·) (positions w false atoms) (positions w true atoms) := by
  induction atoms with
  | nil => simp [positions]
  | cons a atoms ih =>
    apply List.rel_append (a.positions_low_high w)
    simp only [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact ih.imp (fun x y hh => by omega)

private theorem position_low_high (w : ℕ) (atoms : List Atom) (l : Label w atoms) :
    position w atoms false l ≤ position w atoms true l :=
  (positions_low_high w atoms).get l.isLt (by simpa only [positions_length] using l.isLt)

theorem position_gap (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (q : Bool)
    (i j : Label w atoms) (hij : i.val < j.val) :
    position w atoms q i+2 ≤ position w atoms q j := by
  exact (positions_pairwise w hw q atoms).rel_get_of_lt
    (a := ⟨i.val, by simpa only [positions_length] using i.isLt⟩)
    (b := ⟨j.val, by simpa only [positions_length] using j.isLt⟩) hij

/-- Each physical label before the cut is low; every later label is high. -/
def cutPosition (w cut : ℕ) (atoms : List Atom) (l : Label w atoms) : ℕ :=
  if l.val < cut then position w atoms false l else position w atoms true l

/-- Every normal cut keeps a full empty cell between consecutive physical labels. -/
theorem cutPosition_gap (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom)
    (i j : Label w atoms) (hij : i.val < j.val) :
    cutPosition w cut atoms i+2 ≤ cutPosition w cut atoms j := by
  have hlo := position_gap w hw atoms false i j hij
  have hhi := position_gap w hw atoms true i j hij
  have hj := position_low_high w atoms j
  dsimp [cutPosition]
  split_ifs <;> omega

def cutCell (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom) (l : Label w atoms) :
    Cell (width w atoms) (height w) :=
  if l.val < cut then cell w hw atoms false l else cell w hw atoms true l

theorem cutCell_coordinates (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom) (l : Label w atoms) :
    (cutCell w hw cut atoms l).1.val = FiniteTools.radius w+cutPosition w cut atoms l ∧
      (cutCell w hw cut atoms l).2.val = FiniteTools.radius w := by
  dsimp [cutCell, cutPosition]
  split <;> exact ⟨rfl, rfl⟩

attribute [local irreducible] width height

theorem cutCell_injective (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom) :
    Function.Injective (cutCell w hw cut atoms) := by
  intro i j he
  have hi := (cutCell_coordinates w hw cut atoms i).1
  have hj := (cutCell_coordinates w hw cut atoms j).1
  have hx := congrArg (fun p : Cell (width w atoms) (height w) => p.1.val) he
  have hp : cutPosition w cut atoms i = cutPosition w cut atoms j := by omega
  apply Fin.ext
  by_contra hn
  rcases lt_or_gt_of_ne hn with hij | hji
  · have hh := cutPosition_gap w hw cut atoms i j hij; omega
  · have hh := cutPosition_gap w hw cut atoms j i hji; omega

theorem cutCell_order (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom)
    (i j : Label w atoms) (hij : i.val ≤ j.val) :
    (cutCell w hw cut atoms i).1.val ≤ (cutCell w hw cut atoms j).1.val := by
  rcases Nat.eq_or_lt_of_le hij with hh | hh
  · exact Nat.le_of_eq (congrArg (fun l => (cutCell w hw cut atoms l).1.val) (Fin.ext hh))
  · have hg := cutPosition_gap w hw cut atoms i j hh
    have hi := (cutCell_coordinates w hw cut atoms i).1
    have hj := (cutCell_coordinates w hw cut atoms j).1
    omega

def cutBoxes (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom) :
    Finset (Cell (width w atoms) (height w)) := Finset.univ.image (cutCell w hw cut atoms)

theorem cutBoxes_sparse (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom)
    {p q : Cell (width w atoms) (height w)} (hp : p ∈ cutBoxes w hw cut atoms)
    (hq : q ∈ cutBoxes w hw cut atoms) (d : Direction) : ¬Adjacent d p q := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
  have hi := cutCell_coordinates w hw cut atoms i
  have hj := cutCell_coordinates w hw cut atoms j
  intro ha
  by_cases hij : i = j
  · exact ha.ne (congrArg (cutCell w hw cut atoms) hij)
  · have hv : i.val ≠ j.val := fun he => hij (Fin.ext he)
    rcases lt_or_gt_of_ne hv with hv | hv
    · have hg := cutPosition_gap w hw cut atoms i j hv
      cases d <;> simp only [Adjacent] at ha <;> omega
    · have hg := cutPosition_gap w hw cut atoms j i hv
      cases d <;> simp only [Adjacent] at ha <;> omega

def cutFirstLabel (w : ℕ) (atoms : List Atom) : Label w atoms :=
  ⟨0, positions_length_pos w atoms false⟩

def cutLastLabel (w : ℕ) (atoms : List Atom) : Label w atoms :=
  ⟨(positions w false atoms).length-1, by have := positions_length_pos w atoms false; omega⟩

theorem cutCell_first (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom) (hc : 0 < cut) :
    cutCell w hw cut atoms (cutFirstLabel w atoms) = cell w hw atoms false (cutFirstLabel w atoms) := by
  simp [cutCell, cutFirstLabel, hc]

theorem cutCell_last (w : ℕ) (hw : 2 ≤ w) (cut : ℕ) (atoms : List Atom)
    (hc : cut ≤ (positions w false atoms).length-1) :
    cutCell w hw cut atoms (cutLastLabel w atoms) = cell w hw atoms true (cutLastLabel w atoms) := by
  simp [cutCell, cutLastLabel, Nat.not_lt.mpr hc]

end PushPuzzle.PushS.FiniteRouting.Line
