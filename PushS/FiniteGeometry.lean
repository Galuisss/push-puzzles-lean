/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteFreeze
public import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.DeriveFintype

/-! Parameterized thick-wall AND/OR cores for finite pushing. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGeometry

open PushFS

/-- A filled axis-aligned rectangle, including its lower coordinate. -/
structure Rectangle where
  x : ℕ
  y : ℕ
  width : ℕ
  height : ℕ
  deriving DecidableEq

/-- The rectangle restricted to the explicit finite board. -/
def Rectangle.cells (r : Rectangle) (W H : ℕ) : Finset (Cell W H) :=
  Finset.univ.filter fun p =>
    r.x ≤ p.1.val ∧ p.1.val < r.x + r.width ∧
      r.y ≤ p.2.val ∧ p.2.val < r.y + r.height

@[simp] theorem Rectangle.mem_cells (r : Rectangle) (W H : ℕ) (p : Cell W H) :
    p ∈ r.cells W H ↔
      r.x ≤ p.1.val ∧ p.1.val < r.x + r.width ∧
        r.y ≤ p.2.val ∧ p.2.val < r.y + r.height := by
  simp only [cells, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every point of a sufficiently wide rectangle has a filled square cover. -/
theorem Rectangle.squareCovered (r : Rectangle) (W H side : ℕ)
    (hside : 0 < side) (hx : side ≤ r.width) (hy : side ≤ r.height) :
    FiniteFreeze.SquareCovered side (r.cells W H) := by
  intro p hp
  obtain ⟨hpx, hpx', hpy, hpy'⟩ := (r.mem_cells W H p).mp hp
  let x := min p.1.val (r.x + r.width - side)
  let y := min p.2.val (r.y + r.height - side)
  have hxl : r.x ≤ x := by dsimp [x]; omega
  have hyl : r.y ≤ y := by dsimp [y]; omega
  refine ⟨x, y, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [x]; omega
  · dsimp [x]; omega
  · dsimp [y]; omega
  · dsimp [y]; omega
  · intro q hqx hqx' hqy hqy'
    apply (r.mem_cells W H q).mpr
    dsimp [x, y] at *
    omega

/-- All walls in a finite family of thick rectangles have filled square covers. -/
theorem rectangles_squareCovered {n : ℕ} (r : Fin n → Rectangle) (W H side : ℕ) (hside : 0 < side)
    (hr : ∀ i, side ≤ (r i).width ∧ side ≤ (r i).height) :
    FiniteFreeze.SquareCovered side (Finset.univ.biUnion fun i => (r i).cells W H) := by
  intro p hp
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨x, y, hx, hx', hy, hy', hfull⟩ :=
    (r i).squareCovered W H side hside (hr i).1 (hr i).2 p hi
  refine ⟨x, y, hx, hx', hy, hy', ?_⟩
  intro q hqx hqx' hqy hqy'
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hfull q hqx hqx' hqy hqy'⟩

/-- Translation of the integer source coordinates into the finite core board. -/
def origin (w : ℕ) : ℕ := 100 * (w + 3)

/-- A square containing each complete finite core and an exterior walking margin. -/
def side (w : ℕ) : ℕ := 200 * (w + 3)

/-- The seven exact AND wall rectangles in the source geometry. -/
def andRectangle (w : ℕ) (i : Fin 7) : Rectangle :=
  let o := origin w
  match i.val with
  | 0 => ⟨o - 7*w - 9, o + 1, 12*w + 33, w⟩
  | 1 => ⟨o - 7*w - 9, o - 3*w - 9, w, 4*w + 10⟩
  | 2 => ⟨o - 7*w - 9, o - 4*w - 10, w, w⟩
  | 3 => ⟨o - 6*w - 8, o - 3*w - 10, w, w⟩
  | 4 => ⟨o - 6*w - 8, o - 7*w - 21, w, 4*w + 10⟩
  | 5 => ⟨o - 10*w - 26, o - 7*w - 21, 5*w + 18, w⟩
  | _ => ⟨o + 4, o - 10*w - 41, w, 10*w + 41⟩

/-- The two exact OR wall rectangles in the source geometry. -/
def orRectangle (w : ℕ) (i : Fin 2) : Rectangle :=
  let o := origin w
  if i = 0 then ⟨o - 4*w - 17, o + 1, 9*w + 42, w⟩
  else ⟨o + 5, o - 4*w - 23, w, 4*w + 23⟩

theorem andRectangle_thick (w : ℕ) (i : Fin 7) :
    w ≤ (andRectangle w i).width ∧ w ≤ (andRectangle w i).height := by
  fin_cases i <;> simp [andRectangle] <;> omega

theorem orRectangle_thick (w : ℕ) (i : Fin 2) :
    w ≤ (orRectangle w i).width ∧ w ≤ (orRectangle w i).height := by
  fin_cases i <;> simp [orRectangle] <;> omega

/-- Every AND rectangle lies strictly inside the complete explicit board. -/
theorem andRectangle_interior (w : ℕ) (i : Fin 7) :
    0 < (andRectangle w i).x ∧ 0 < (andRectangle w i).y ∧
      (andRectangle w i).x + (andRectangle w i).width < side w ∧
      (andRectangle w i).y + (andRectangle w i).height < side w := by
  fin_cases i <;> simp [andRectangle, origin, side] <;> omega

theorem orRectangle_interior (w : ℕ) (i : Fin 2) :
    0 < (orRectangle w i).x ∧ 0 < (orRectangle w i).y ∧
      (orRectangle w i).x + (orRectangle w i).width < side w ∧
      (orRectangle w i).y + (orRectangle w i).height < side w := by
  fin_cases i <;> simp [orRectangle, origin, side] <;> omega

/-- The virtual walls of the complete AND core. -/
def andWalls (w : ℕ) : Finset (Cell (side w) (side w)) :=
  Finset.univ.biUnion fun i => (andRectangle w i).cells (side w) (side w)

/-- The virtual walls of the complete OR core. -/
def orWalls (w : ℕ) : Finset (Cell (side w) (side w)) :=
  Finset.univ.biUnion fun i => (orRectangle w i).cells (side w) (side w)

private theorem andWalls_squareCovered (w : ℕ) (hw : 0 < w) : FiniteFreeze.SquareCovered w
    (andWalls w) :=
  rectangles_squareCovered (andRectangle w) (side w) (side w) w hw (andRectangle_thick w)

private theorem orWalls_squareCovered (w : ℕ) (hw : 0 < w) : FiniteFreeze.SquareCovered w
    (orWalls w) :=
  rectangles_squareCovered (orRectangle w) (side w) (side w) w hw (orRectangle_thick w)

/-- At width `k+1`, the actual AND wall cells satisfy the freezing hypothesis. -/
theorem andWalls_thick (k : ℕ) : FiniteFreeze.Thick k (andWalls (k+1)) :=
  FiniteFreeze.thick_of_squareCovered (by omega) (andWalls_squareCovered (k+1) (by omega))

theorem orWalls_thick (k : ℕ) : FiniteFreeze.Thick k (orWalls (k+1)) :=
  FiniteFreeze.thick_of_squareCovered (by omega) (orWalls_squareCovered (k+1) (by omega))

/-- Physical identities of every normal AND working box. -/
inductive AndLabel (w : ℕ)
  | west (i : Fin (w+4))
  | upper (i : Fin (w+5))
  | middle
  | lower (i : Fin (w+5))
  | guard (i : Fin (3*w+5))
  | triggerA
  | branchB (i : Fin (4*w+16))
  | branchC (i : Fin (w+5))
  deriving DecidableEq, Fintype

/-- Physical identities of every normal OR working box. -/
inductive OrLabel (w : ℕ)
  | left (i : Fin (w+5))
  | triggerA
  | branchB (i : Fin (w+7))
  | branchC (i : Fin (w+5))
  deriving DecidableEq, Fintype

/-- AND normal positions: `a,b` are input inflows and `c` is output outflow. -/
def andPoint (w : ℕ) (a b c : Bool) : AndLabel w → ℕ × ℕ
  | .west i => (origin w - 6*w - 10 - 2*i.val - a.toNat, origin w - 6*w - 21)
  | .upper i => (origin w - 6*w - 9, origin w - 6*w - 19 + 2*i.val - a.toNat)
  | .middle => (origin w - 6*w - 9, origin w - 3*w - 9 - 3*a.toNat)
  | .lower i => (origin w - 6*w - 9, origin w - 2*w - 9 + 2*i.val - a.toNat)
  | .guard i => (origin w - 6*w - 7 + 2*i.val - a.toNat, origin w)
  | .triggerA => (origin w + 3 - a.toNat, origin w)
  | .branchB i => (origin w + 3, origin w - 1 - 2*i.val - b.toNat)
  | .branchC i => (origin w + w + 5 + 2*i.val - c.toNat, origin w)

/-- OR normal positions with the same input/output convention. -/
def orPoint (w : ℕ) (a b c : Bool) : OrLabel w → ℕ × ℕ
  | .left i => (origin w + 1 - 2*i.val - a.toNat, origin w)
  | .triggerA => (origin w + 3 - a.toNat, origin w)
  | .branchB i => (origin w + 4, origin w - 1 - 2*i.val - b.toNat)
  | .branchC i => (origin w + w + 6 + 2*i.val - c.toNat, origin w)

theorem andPoint_interior (w : ℕ) (a b c : Bool) (l : AndLabel w) :
    0 < (andPoint w a b c l).1 ∧ (andPoint w a b c l).1 < side w ∧
      0 < (andPoint w a b c l).2 ∧ (andPoint w a b c l).2 < side w := by
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  cases l <;> dsimp [andPoint, origin, side] <;> omega

theorem orPoint_interior (w : ℕ) (a b c : Bool) (l : OrLabel w) :
    0 < (orPoint w a b c l).1 ∧ (orPoint w a b c l).1 < side w ∧
      0 < (orPoint w a b c l).2 ∧ (orPoint w a b c l).2 < side w := by
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  cases l <;> dsimp [orPoint, origin, side] <;> omega

/-- The normal AND working boxes as actual bounded cells. -/
def andCell (w : ℕ) (a b c : Bool) (l : AndLabel w) : Cell (side w) (side w) :=
  (⟨(andPoint w a b c l).1, (andPoint_interior w a b c l).2.1⟩,
   ⟨(andPoint w a b c l).2, (andPoint_interior w a b c l).2.2.2⟩)

def orCell (w : ℕ) (a b c : Bool) (l : OrLabel w) : Cell (side w) (side w) :=
  (⟨(orPoint w a b c l).1, (orPoint_interior w a b c l).2.1⟩,
   ⟨(orPoint w a b c l).2, (orPoint_interior w a b c l).2.2.2⟩)

attribute [local irreducible] side

set_option maxRecDepth 8192 in
/-- Every normal working position lies outside every AND wall rectangle. -/
theorem andCell_not_wall (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) (l : AndLabel w) :
    andCell w a b c l ∉ andWalls w := by
  intro hp
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
  have hi' := ((andRectangle w i).mem_cells _ _ _).mp hi
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  fin_cases i <;> cases l <;>
    simp [andRectangle, andCell, andPoint, origin] at hi' <;> omega

set_option maxRecDepth 8192 in
theorem orCell_not_wall (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) (l : OrLabel w) :
    orCell w a b c l ∉ orWalls w := by
  intro hp
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
  have hi' := ((orRectangle w i).mem_cells _ _ _).mp hi
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  fin_cases i <;> cases l <;>
    simp [orRectangle, orCell, orPoint, origin] at hi' <;> omega

/-- The complete unlabelled normal AND working inventory. -/
def andBoxes (w : ℕ) (a b c : Bool) : Finset (Cell (side w) (side w)) :=
  Finset.univ.image (andCell w a b c)

def orBoxes (w : ℕ) (a b c : Bool) : Finset (Cell (side w) (side w)) :=
  Finset.univ.image (orCell w a b c)

theorem andBoxes_disjoint_walls (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) :
    Disjoint (andBoxes w a b c) (andWalls w) := by
  apply Finset.disjoint_left.mpr
  intro p hp
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
  exact andCell_not_wall w hw a b c l

theorem orBoxes_disjoint_walls (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) :
    Disjoint (orBoxes w a b c) (orWalls w) := by
  apply Finset.disjoint_left.mpr
  intro p hp
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
  exact orCell_not_wall w hw a b c l

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- The indexed normal AND boxes occupy pairwise distinct physical cells. -/
theorem andCell_injective (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) :
    Function.Injective (andCell w a b c) := by
  intro l m he
  have hx := congrArg (fun p => p.1.val) he
  have hy := congrArg (fun p => p.2.val) he
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  cases l <;> cases m <;> simp [andCell, andPoint, origin] at hx hy
  all_goals first | rfl | (congr 1; apply Fin.ext; omega) | omega

set_option maxRecDepth 8192 in
theorem orCell_injective (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) :
    Function.Injective (orCell w a b c) := by
  intro l m he
  have hx := congrArg (fun p => p.1.val) he
  have hy := congrArg (fun p => p.2.val) he
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  cases l <;> cases m <;> simp [orCell, orPoint, origin] at hx hy
  all_goals first | rfl | (congr 1; apply Fin.ext; omega) | omega

/-- Every normal phase has the same complete AND inventory. -/
theorem andBoxes_card (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) :
    (andBoxes w a b c).card = Fintype.card (AndLabel w) := by
  rw [andBoxes, Finset.card_image_of_injective _ (andCell_injective w hw a b c)]
  exact Finset.card_univ

theorem orBoxes_card (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) :
    (orBoxes w a b c).card = Fintype.card (OrLabel w) := by
  rw [orBoxes, Finset.card_image_of_injective _ (orCell_injective w hw a b c)]
  exact Finset.card_univ

/-- Normal working boxes leave the board's top and left boundary empty. -/
private theorem andBoxes_positive (w : ℕ) (a b c : Bool) {p : Cell (side w) (side w)}
    (hp : p ∈ andBoxes w a b c) : 0 < p.1.val ∧ 0 < p.2.val := by
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
  exact ⟨(andPoint_interior w a b c l).1, (andPoint_interior w a b c l).2.2.1⟩

private theorem orBoxes_positive (w : ℕ) (a b c : Bool) {p : Cell (side w) (side w)}
    (hp : p ∈ orBoxes w a b c) : 0 < p.1.val ∧ 0 < p.2.val := by
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
  exact ⟨(orPoint_interior w a b c l).1, (orPoint_interior w a b c l).2.2.1⟩

private theorem andWalls_positive (w : ℕ) {p : Cell (side w) (side w)}
    (hp : p ∈ andWalls w) : 0 < p.1.val ∧ 0 < p.2.val := by
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
  have hi' := ((andRectangle w i).mem_cells _ _ _).mp hi
  have hb := andRectangle_interior w i
  omega

private theorem orWalls_positive (w : ℕ) {p : Cell (side w) (side w)}
    (hp : p ∈ orWalls w) : 0 < p.1.val ∧ 0 < p.2.val := by
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
  have hi' := ((orRectangle w i).mem_cells _ _ _).mp hi
  have hb := orRectangle_interior w i
  omega

/-- A common empty initial player cell in the exterior margin. -/
def corner (w : ℕ) : Cell (side w) (side w) :=
  (⟨0, by unfold side; omega⟩, ⟨0, by unfold side; omega⟩)

theorem corner_not_andBoxes (w : ℕ) (a b c : Bool) : corner w ∉ andBoxes w a b c := by
  intro hp
  have := (andBoxes_positive w a b c hp).1
  change 0 < 0 at this
  omega

theorem corner_not_orBoxes (w : ℕ) (a b c : Bool) : corner w ∉ orBoxes w a b c := by
  intro hp
  have := (orBoxes_positive w a b c hp).1
  change 0 < 0 at this
  omega

theorem corner_not_andWalls (w : ℕ) : corner w ∉ andWalls w := by
  intro hp
  have := (andWalls_positive w hp).1
  change 0 < 0 at this
  omega

theorem corner_not_orWalls (w : ℕ) : corner w ∉ orWalls w := by
  intro hp
  have := (orWalls_positive w hp).1
  change 0 < 0 at this
  omega

end PushPuzzle.PushS.FiniteGeometry
