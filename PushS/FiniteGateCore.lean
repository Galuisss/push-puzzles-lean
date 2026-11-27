/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGeometry
public import PushS.FiniteCavity
public import PushS.FiniteWalls
public import PushFS.Gadgets.Gates.Basic

/-! Actual thick gate walls and the normal threshold configurations. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateCore

open PushFS FiniteGeometry
open PushFS.Gadgets

attribute [local irreducible] side

/-- The fixed-wall AND core, before its uniform tails are attached to the routing. -/
def andBoard (w : ℕ) (goals : Finset (Cell (side w) (side w))) :
    Board (side w) (side w) := ⟨andWalls w, goals⟩

def orBoard (w : ℕ) (goals : Finset (Cell (side w) (side w))) :
    Board (side w) (side w) := ⟨orWalls w, goals⟩

/-- The seven concrete rectangles provide the walls of the AND contraction cavity. -/
theorem andCavityWalls (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w))) :
    FiniteCavity.Walls (andBoard w goals) (origin w + 3) (origin w + w + 4) (origin w) := by
  constructor
  · intro p hy hx hx'
    change p ∈ andWalls w
    apply Finset.mem_biUnion.mpr
    refine ⟨0, Finset.mem_univ _, ?_⟩
    apply (Rectangle.mem_cells (andRectangle w 0) (side w) (side w) p).mpr
    simp [andRectangle, origin] at *
    omega
  · intro p hy hx
    change p ∈ andWalls w
    apply Finset.mem_biUnion.mpr
    refine ⟨6, Finset.mem_univ _, ?_⟩
    apply (Rectangle.mem_cells (andRectangle w 6) (side w) (side w) p).mpr
    simp [andRectangle, origin] at *
    omega

theorem orCavityWalls (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w))) :
    FiniteCavity.Walls (orBoard w goals) (origin w + 4) (origin w + w + 5) (origin w) := by
  constructor
  · intro p hy hx hx'
    change p ∈ orWalls w
    apply Finset.mem_biUnion.mpr
    refine ⟨0, Finset.mem_univ _, ?_⟩
    apply (Rectangle.mem_cells (orRectangle w 0) (side w) (side w) p).mpr
    simp only [orRectangle, ite_true, origin] at *
    omega
  · intro p hy hx
    change p ∈ orWalls w
    apply Finset.mem_biUnion.mpr
    refine ⟨1, Finset.mem_univ _, ?_⟩
    apply (Rectangle.mem_cells (orRectangle w 1) (side w) (side w) p).mpr
    simp only [orRectangle, show (1 : Fin 2) ≠ 0 from by decide, ite_false, origin] at *
    omega

/-- The common exterior corner used to enter a complete finite core. -/
def hub (w : ℕ) : Cell (side w) (side w) :=
  corner w

def andState (w : ℕ) (a b c : Bool) : State (side w) (side w) :=
  ⟨hub w, andBoxes w a b c⟩

def orState (w : ℕ) (a b c : Bool) : State (side w) (side w) :=
  ⟨hub w, orBoxes w a b c⟩

/-- The three AND triggers retain their physical identities among the full inventory. -/
def andConfiguration (w : ℕ) (a b c : Bool) : AND.Configuration (side w) (side w) :=
  ⟨andState w a b c, andCell w a b c .triggerA,
    andCell w a b c (.branchB 0), andCell w a b c (.branchC 0)⟩

def orConfiguration (w : ℕ) (a b c : Bool) : AND.Configuration (side w) (side w) :=
  ⟨orState w a b c, orCell w a b c .triggerA,
    orCell w a b c (.branchB 0), orCell w a b c (.branchC 0)⟩

theorem andConfiguration_shape (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) :
    AND.Shape (origin w + 3) (origin w) (andConfiguration w a b c) := by
  have ha : a.toNat ≤ 1 := by cases a <;> decide
  have hb : b.toNat ≤ 1 := by cases b <;> decide
  have hc : c.toNat ≤ 1 := by cases c <;> decide
  constructor
  · exact Finset.mem_image.mpr ⟨.triggerA, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨.branchB 0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨.branchC 0, Finset.mem_univ _, rfl⟩
  all_goals first | rfl | (dsimp [andConfiguration, andCell, andPoint, origin]; omega)

theorem orConfiguration_shape (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) :
    OR.Shape (origin w + 4) (origin w) (orConfiguration w a b c) := by
  have ha : a.toNat ≤ 1 := by cases a <;> decide
  have hb : b.toNat ≤ 1 := by cases b <;> decide
  have hc : c.toNat ≤ 1 := by cases c <;> decide
  constructor
  · exact Finset.mem_image.mpr ⟨.triggerA, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨.branchB 0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨.branchC 0, Finset.mem_univ _, rfl⟩
  all_goals first | rfl | (dsimp [orConfiguration, orCell, orPoint, origin]; omega)

/-- On normal slots, the geometric AND threshold is exactly its NCL gate relation. -/
theorem andConfiguration_good_iff (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) :
    FiniteCavity.AND.Good (origin w + 3) (origin w + w + 4) (origin w)
      (andConfiguration w a b c) ↔ (c = true → a = true ∧ b = true) := by
  cases a <;> cases b <;> cases c <;>
    simp [FiniteCavity.AND.Good, andConfiguration, andCell, andPoint, origin] <;> omega

theorem orConfiguration_good_iff (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) :
    FiniteCavity.OR.Good (origin w + 4) (origin w + w + 5) (origin w)
      (orConfiguration w a b c) ↔ (c = true → a = true ∨ b = true) := by
  cases a <;> cases b <;> cases c <;>
    simp [FiniteCavity.OR.Good, orConfiguration, orCell, orPoint, origin] <;> omega

theorem andState_valid (w : ℕ) (hw : 2 ≤ w) (a b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    (andState w a b c).Valid (andBoard w goals) :=
  ⟨corner_not_andWalls w, andBoxes_disjoint_walls w hw a b c,
    corner_not_andBoxes w a b c⟩

theorem orState_valid (w : ℕ) (hw : 2 ≤ w) (a b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    (orState w a b c).Valid (orBoard w goals) :=
  ⟨corner_not_orWalls w, orBoxes_disjoint_walls w hw a b c,
    corner_not_orBoxes w a b c⟩

/-- The complete finite AND core with every auxiliary box included in the targets. -/
def andInstance (w : ℕ) (hw : 2 ≤ w) (initial target : Gates.Signals) : PushFS.Instance where
  width := side w
  height := side w
  board := andBoard w (andBoxes w target.left target.upper target.right)
  initial := andState w initial.left initial.upper initial.right
  goals_floor := (andBoxes_disjoint_walls w hw target.left target.upper target.right).symm
  initial_valid := andState_valid w hw initial.left initial.upper initial.right _
  boxes_eq_goals := (andBoxes_card w hw _ _ _).trans (andBoxes_card w hw _ _ _).symm

def orInstance (w : ℕ) (hw : 2 ≤ w) (initial target : Gates.Signals) : PushFS.Instance where
  width := side w
  height := side w
  board := orBoard w (orBoxes w target.left target.upper target.right)
  initial := orState w initial.left initial.upper initial.right
  goals_floor := (orBoxes_disjoint_walls w hw target.left target.upper target.right).symm
  initial_valid := orState_valid w hw initial.left initial.upper initial.right _
  boxes_eq_goals := (orBoxes_card w hw _ _ _).trans (orBoxes_card w hw _ _ _).symm

/-- The AND core as a genuinely wall-free finite-pushing storage instance. -/
noncomputable def andStorage (k : ℕ) (hk : 1 ≤ k) (initial target : Gates.Signals) : Instance :=
  FiniteWalls.fillWalls (andInstance (k+1) (by omega) initial target)

noncomputable def orStorage (k : ℕ) (hk : 1 ≤ k) (initial target : Gates.Signals) : Instance :=
  FiniteWalls.fillWalls (orInstance (k+1) (by omega) initial target)

theorem andStorage_solvable_iff (k : ℕ) (hk : 1 ≤ k) (initial target : Gates.Signals) :
    (andStorage k hk initial target).SolvableFinite k ↔
      (andInstance (k+1) (by omega) initial target).Solvable (some k) :=
  FiniteWalls.fillWalls_solvable_iff _ (andWalls_thick k)

theorem orStorage_solvable_iff (k : ℕ) (hk : 1 ≤ k) (initial target : Gates.Signals) :
    (orStorage k hk initial target).SolvableFinite k ↔
      (orInstance (k+1) (by omega) initial target).Solvable (some k) :=
  FiniteWalls.fillWalls_solvable_iff _ (orWalls_thick k)

end PushPuzzle.PushS.FiniteGateCore
