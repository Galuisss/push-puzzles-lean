/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingCoreSeparation
public import PushS.FiniteRoutingLineEndpoints

/-! Actual wall and actor separation at the initial core-to-arm interface. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction FiniteGeometry

attribute [local irreducible] FiniteGeometry.side

def Outward (d : Direction) (p a : ℕ × ℕ) : Prop :=
  match d with
  | .east => p.1 ≤ a.1
  | .south => p.2 ≤ a.2
  | .west => a.1 ≤ p.1
  | .north => a.2 ≤ p.2

def SameLane (d : Direction) (p a : ℕ × ℕ) : Prop :=
  match d with
  | .east | .west => p.2 = a.2
  | .north | .south => p.1 = a.1

namespace Line

attribute [local irreducible] width height

/-- Every actual strip wall lies forward of its no-inflow start and off the working lane. -/
theorem placed_wall_side (w : ℕ) (atoms : List Atom) (above : Bool)
    (d : Direction) (p q : ℕ × ℕ) (htravel : Travels d p q (span w atoms))
    (hp : p.1 ≤ tileStride w ∧ p.2 ≤ tileStride w)
    (hq : q.1 ≤ tileStride w ∧ q.2 ≤ tileStride w)
    (a : Cell (width w atoms) (height w)) (ha : a ∈ walls w atoms above) :
    Outward d (along w d p 0) (coordinates ((placement w atoms d p q htravel hp hq).cells a)) ∧
      ¬SameLane d (along w d p 0) (coordinates ((placement w atoms d p q htravel hp hq).cells a)) := by
  have hb := walls_bounds w atoms above ha
  have hn : a.2.val ≠ FiniteTools.radius w := fun hy => row_floor w atoms above a hy ha
  have hr := rotation_coordinates w atoms d a
  have hx := congrArg Prod.fst hr
  have hy := congrArg Prod.snd hr
  dsimp only at hx hy
  dsimp [coordinates, placement, GridEmbedding.trans, GridEmbedding.translate, GridIsometry.embedding]
  rw [hx,hy]
  have haX := a.1.isLt
  have haY := a.2.isLt
  cases d <;> dsimp [rotatedCoordinates,Outward,SameLane,along,Travels,offsetX,offsetY,anchor] at * <;>
    unfold width height FiniteTools.side FiniteTools.radius padding at * <;> omega

end Line

set_option maxRecDepth 65536 in
theorem andActor_outward_lane (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) (role : Fin 3)
    (l : AndLabel w)
    (h : Outward (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w true role) 0)
      (coreWorld w (andCell w a b c l))) :
    SameLane (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w true role) 0)
      (coreWorld w (andCell w a b c l)) := by
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  cases l <;> fin_cases role <;>
    simp [Outward,SameLane,PortAnnulus.innerDirection,Line.along,corePort,coreWorld,andCell,
      andPoint,origin,coreOffset,padding,spacing] at * <;> omega

set_option maxRecDepth 65536 in
theorem orActor_outward_lane (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) (role : Fin 3)
    (l : OrLabel w)
    (h : Outward (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w false role) 0)
      (coreWorld w (orCell w a b c l))) :
    SameLane (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w false role) 0)
      (coreWorld w (orCell w a b c l)) := by
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  cases l <;> fin_cases role <;>
    simp [Outward,SameLane,PortAnnulus.innerDirection,Line.along,corePort,coreWorld,orCell,
      orPoint,origin,coreOffset,padding,spacing] at * <;> omega

theorem andPort_world (w : ℕ) (a b c : Bool) (role : Fin 3) :
    coreWorld w (andCell w a b c (andPortLabel w role)) =
      Line.along w (PortAnnulus.innerDirection role) (corePort w true role)
        (portInflow a b c role).toNat := by
  have h := andPort_position w a b c role
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases role <;> apply Prod.ext <;>
    simp [coreWorld,andCell,Line.along,PortAnnulus.innerDirection,portPosition,corePort,
      portInflow,spacing,padding] at * <;> omega

theorem orPort_world (w : ℕ) (a b c : Bool) (role : Fin 3) :
    coreWorld w (orCell w a b c (orPortLabel w role)) =
      Line.along w (PortAnnulus.innerDirection role) (corePort w false role)
        (portInflow a b c role).toNat := by
  have h := orPort_position w a b c role
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases role <;> apply Prod.ext <;>
    simp [coreWorld,orCell,Line.along,PortAnnulus.innerDirection,portPosition,corePort,
      portInflow,spacing,padding] at * <;> omega

end PushPuzzle.PushS.FiniteRouting
