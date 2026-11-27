/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineFrame
public import PushS.FiniteRoutingPlacement

/-! Literal coordinates of both exposed starting faces of every oriented complete line. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line

open PushFS

attribute [local irreducible] width height

/-- Both exposed start faces lie one step forward and `w+1` cells to the selected side. -/
def outerStart (w : ℕ) (d : Direction) (p : ℕ × ℕ) (north : Bool) : ℕ × ℕ :=
  match d with
  | .east => (padding w+p.1+1,if north then padding w+p.2-(w+1) else padding w+p.2+(w+1))
  | .south => (if north then padding w+p.1+(w+1) else padding w+p.1-(w+1),padding w+p.2+1)
  | .west => (padding w+p.1-1,if north then padding w+p.2+(w+1) else padding w+p.2-(w+1))
  | .north => (if north then padding w+p.1-(w+1) else padding w+p.1+(w+1),padding w+p.2-1)

/-- The actual oriented line placement maps its two start-face hubs to their literal world coordinates. -/
theorem placement_outerStart (w : ℕ) (atoms : List Atom) (d : Direction) (p q : ℕ × ℕ)
    (htravel : Travels d p q (span w atoms))
    (hp : p.1 ≤ tileStride w ∧ p.2 ≤ tileStride w)
    (hq : q.1 ≤ tileStride w ∧ q.2 ≤ tileStride w) (north : Bool) :
    (((placement w atoms d p q htravel hp hq).cells
        (outerCell w atoms north (outerHubX w atoms))).1.val,
      ((placement w atoms d p q htravel hp hq).cells
        (outerCell w atoms north (outerHubX w atoms))).2.val) = outerStart w d p north := by
  have hr := rotation_coordinates w atoms d (outerCell w atoms north (outerHubX w atoms))
  have hx := congrArg Prod.fst hr
  have hy := congrArg Prod.snd hr
  dsimp only at hx hy
  apply Prod.ext
  all_goals dsimp [placement, GridEmbedding.trans, GridEmbedding.translate, GridIsometry.embedding]
  · rw [hx]
    cases d <;> cases north <;>
      dsimp [rotatedCoordinates,outerCell,outerHubX,laneY,outerStart,Travels,offsetX,anchor] at * <;>
      unfold width height FiniteTools.side FiniteTools.radius padding at * <;> omega
  · rw [hy]
    cases d <;> cases north <;>
      dsimp [rotatedCoordinates,outerCell,outerHubX,laneY,outerStart,Travels,offsetY,anchor] at * <;>
      unfold width height FiniteTools.side FiniteTools.radius padding at * <;> omega

end PushPuzzle.PushS.FiniteRouting.Line
