/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGeometry
public import PushFS.Walking
import Mathlib.Tactic.FinCases

/-! Parameterized thick flip and parity tools, including their actual exterior neighbors. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteTools

open PushFS FiniteGeometry

/-- Radius of the finite tool window around the source origin. -/
def radius (w : ℕ) : ℕ := 2*w + 12

def side (w : ℕ) : ℕ := 2 * radius w + 1

/-- The least odd roof width at least both three and the wall width. -/
def paritySpan (w : ℕ) : ℕ := 2 * (max 3 w / 2) + 1

theorem paritySpan_bounds (w : ℕ) :
    3 ≤ paritySpan w ∧ w ≤ paritySpan w ∧ paritySpan w ≤ w + 3 := by
  unfold paritySpan
  omega

theorem paritySpan_odd (w : ℕ) : paritySpan w % 2 = 1 := by
  unfold paritySpan
  omega

/-- Lower tail, lower island, upper island, and upper tail of the thick flip. -/
def flipRectangle (w : ℕ) (i : Fin 4) : Rectangle :=
  let r := radius w
  match i.val with
  | 0 => ⟨0, r+1, r+1, w⟩
  | 1 => ⟨r+2, r+1, w, w⟩
  | 2 => ⟨r+2-w, r-w, w, w⟩
  | _ => ⟨r+3, r-w, r-2, w⟩

/-- The lower rail and the odd upper roof of the parity adapter. -/
def parityRectangle (w : ℕ) (i : Fin 2) : Rectangle :=
  if i = 0 then ⟨0, radius w+1, side w, w⟩
  else ⟨radius w+2, radius w-w, paritySpan w, w⟩

def flipWalls (w : ℕ) : Finset (Cell (side w) (side w)) :=
  Finset.univ.biUnion fun i => (flipRectangle w i).cells (side w) (side w)

def parityWalls (w : ℕ) : Finset (Cell (side w) (side w)) :=
  Finset.univ.biUnion fun i => (parityRectangle w i).cells (side w) (side w)

/-- The fixed real exterior neighbors and the three working flip boxes. -/
inductive FlipLabel
  | predecessor | left | middle | right | successor
  deriving DecidableEq

instance : Fintype FlipLabel where
  elems := {.predecessor, .left, .middle, .right, .successor}
  complete l := by cases l <;> simp

/-- The fixed real exterior neighbors and the two working parity boxes. -/
inductive ParityLabel
  | predecessor | left | right | successor
  deriving DecidableEq

instance : Fintype ParityLabel where
  elems := {.predecessor, .left, .right, .successor}
  complete l := by cases l <;> simp

def flipPoint (w : ℕ) (q : Bool) : FlipLabel → ℕ × ℕ
  | .predecessor => (radius w-w-2, radius w)
  | .left => (radius w-w+q.toNat, radius w)
  | .middle => (radius w+3*q.toNat, radius w)
  | .right => (radius w+w+2+q.toNat, radius w)
  | .successor => (radius w+w+5, radius w)

def parityPoint (w : ℕ) (q : Bool) : ParityLabel → ℕ × ℕ
  | .predecessor => (radius w-2, radius w)
  | .left => (radius w+q.toNat, radius w)
  | .right => (radius w+paritySpan w+2+q.toNat, radius w)
  | .successor => (radius w+paritySpan w+5, radius w)

theorem flipPoint_interior (w : ℕ) (q : Bool) (l : FlipLabel) :
    0 < (flipPoint w q l).1 ∧ (flipPoint w q l).1 < side w ∧
      0 < (flipPoint w q l).2 ∧ (flipPoint w q l).2 < side w := by
  have hq := Bool.toNat_le q
  cases l <;> dsimp [flipPoint, radius, side] <;> omega

theorem parityPoint_interior (w : ℕ) (q : Bool) (l : ParityLabel) :
    0 < (parityPoint w q l).1 ∧ (parityPoint w q l).1 < side w ∧
      0 < (parityPoint w q l).2 ∧ (parityPoint w q l).2 < side w := by
  have hq := Bool.toNat_le q
  have hm := paritySpan_bounds w
  cases l <;> dsimp [parityPoint, radius, side] <;> omega

def flipCell (w : ℕ) (q : Bool) (l : FlipLabel) : Cell (side w) (side w) :=
  (⟨(flipPoint w q l).1, (flipPoint_interior w q l).2.1⟩,
   ⟨(flipPoint w q l).2, (flipPoint_interior w q l).2.2.2⟩)

def parityCell (w : ℕ) (q : Bool) (l : ParityLabel) : Cell (side w) (side w) :=
  (⟨(parityPoint w q l).1, (parityPoint_interior w q l).2.1⟩,
   ⟨(parityPoint w q l).2, (parityPoint_interior w q l).2.2.2⟩)

private theorem flipCell_not_wall (w : ℕ) (q : Bool) (l : FlipLabel) :
    flipCell w q l ∉ flipWalls w := by
  intro hp
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
  have hi' := ((flipRectangle w i).mem_cells _ _ _).mp hi
  fin_cases i <;> cases l <;>
    simp [flipRectangle, flipCell, flipPoint, radius] at hi' <;> omega

theorem parityCell_not_wall (w : ℕ) (q : Bool) (l : ParityLabel) :
    parityCell w q l ∉ parityWalls w := by
  intro hp
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
  have hi' := ((parityRectangle w i).mem_cells _ _ _).mp hi
  fin_cases i <;> cases l <;>
    simp [parityRectangle, parityCell, parityPoint, radius] at hi' <;> omega

def flipBoxes (w : ℕ) (q : Bool) : Finset (Cell (side w) (side w)) :=
  Finset.univ.image (flipCell w q)

def parityBoxes (w : ℕ) (q : Bool) : Finset (Cell (side w) (side w)) :=
  Finset.univ.image (parityCell w q)

private theorem flipBoxes_disjoint_walls (w : ℕ) (q : Bool) :
    Disjoint (flipBoxes w q) (flipWalls w) := by
  apply Finset.disjoint_left.mpr
  intro p hp
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
  exact flipCell_not_wall w q l

/-- The adjacent lower and upper crossing mouths of the flip. -/
def crossingCell (w : ℕ) (i : Fin 4) : Cell (side w) (side w) :=
  (⟨radius w + if i.val < 2 then 1 else 2, by unfold side radius; split <;> omega⟩,
   ⟨if i.val = 0 then radius w+1 else if i.val = 3 then radius w-1 else radius w, by
      unfold side radius
      split
      · omega
      · split <;> omega⟩)

private theorem crossingCell_not_wall (w : ℕ) (i : Fin 4) : crossingCell w i ∉ flipWalls w := by
  intro hp
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
  have hj' := ((flipRectangle w j).mem_cells _ _ _).mp hj
  fin_cases i <;> fin_cases j <;>
    simp [crossingCell, flipRectangle, radius] at hj' <;> omega

private theorem crossingCell_not_box (w : ℕ) (hw : 2 ≤ w) (q : Bool) (i : Fin 4) :
    crossingCell w i ∉ flipBoxes w q := by
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hx := congrArg (fun p : Cell (side w) (side w) => p.1.val) he
  have hy := congrArg (fun p : Cell (side w) (side w) => p.2.val) he
  have hq := Bool.toNat_le q
  fin_cases i <;> cases l <;>
    simp [crossingCell, flipCell, flipPoint, radius] at hx hy <;> omega

/-- Both normal phases permit the same real three-step walk across the thick flip. -/
theorem flip_crossing (w : ℕ) (hw : 2 ≤ w) (q : Bool) :
    Reachable ⟨flipWalls w, flipBoxes w q⟩ (some 1)
      ⟨crossingCell w 0, flipBoxes w q⟩ ⟨crossingCell w 3, flipBoxes w q⟩ := by
  apply walk_fin_path (flipBoxes_disjoint_walls w q) (crossingCell w)
  · intro i
    exact ⟨crossingCell_not_wall w i, crossingCell_not_box w hw q i⟩
  · intro i
    fin_cases i
    · exact ⟨.north, by simp [Adjacent, crossingCell]⟩
    · exact ⟨.east, by simp [Adjacent, crossingCell]⟩
    · exact ⟨.north, by simp [Adjacent, crossingCell, radius]⟩

end PushPuzzle.PushS.FiniteTools
