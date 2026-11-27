/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingInitial
public import PushS.FiniteRoutingLineStock
public import PushS.FiniteGateOuterAccess
public import PushS.FiniteFramePlacement

/-! Initial-arm wall sides needed by the literal gate-to-line walking corridors. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction FiniteGeometry

namespace Line

attribute [local irreducible] width height program initialAtoms budget span

/-- The closed perpendicular band of width `w` around an oriented literal starting rail. -/
def PerpendicularBand (w : ℕ) (d : Direction) (a p : ℕ × ℕ) : Prop :=
  match d with
  | .east | .west => a.2 ≤ p.2+w ∧ p.2 ≤ a.2+w
  | .north | .south => a.1 ≤ p.1+w ∧ p.1 ≤ a.1+w

/-- All actual placed line walls lie in their literal perpendicular width-`w` band. -/
theorem placed_wall_band (w : ℕ) (atoms : List Atom) (above : Bool)
    (d : Direction) (p q : ℕ × ℕ) (ht : Travels d p q (span w atoms))
    (hp : p.1 ≤ tileStride w ∧ p.2 ≤ tileStride w)
    (hq : q.1 ≤ tileStride w ∧ q.2 ≤ tileStride w)
    (a : Cell (width w atoms) (height w)) (ha : a ∈ walls w atoms above) :
    PerpendicularBand w d (along w d p 0)
      (coordinates ((placement w atoms d p q ht hp hq).cells a)) := by
  have hb := walls_bounds w atoms above ha
  have hr := rotation_coordinates w atoms d a
  have hx := congrArg Prod.fst hr
  have hy := congrArg Prod.snd hr
  dsimp only at hx hy
  dsimp [coordinates,placement,GridEmbedding.trans,GridEmbedding.translate,GridIsometry.embedding]
  rw [hx,hy]
  cases d <;> dsimp [PerpendicularBand,rotatedCoordinates,along,offsetX,offsetY,anchor] at * <;>
    unfold width height FiniteTools.side FiniteTools.radius padding at * <;> omega

/-- A physical point in the first one-step column of an outward oriented line. -/
def FirstColumn (d : Direction) (a p : ℕ × ℕ) : Prop :=
  match d with
  | .east => p.1 ≤ a.1+1
  | .south => p.2 ≤ a.2+1
  | .west => a.1 ≤ p.1+1
  | .north => a.2 ≤ p.2+1

/-- The world-space side of a proper rotation of an above/below protecting wall. -/
def GuardSide (d : Direction) (above : Bool) (a p : ℕ × ℕ) : Prop :=
  match d with
  | .east => if above then p.2 < a.2 else a.2 < p.2
  | .south => if above then a.1 < p.1 else p.1 < a.1
  | .west => if above then a.2 < p.2 else p.2 < a.2
  | .north => if above then p.1 < a.1 else a.1 < p.1

end Line

end PushPuzzle.PushS.FiniteRouting
