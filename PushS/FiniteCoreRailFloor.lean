/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteCoreRailSeparation
public import PushS.FiniteRoutingGateGeometry
public import PushS.FiniteCoreRails

/-! Complete core support rails remain floor under all three actual arm wall families. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction FiniteGeometry FiniteGateMatching

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem world_injective (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) :
    Function.Injective (c.world w hw) := by
  intro p q he
  apply Prod.ext <;> apply Fin.ext
  · have hx := congrArg Prod.fst he
    dsimp [PrimitiveCode.world] at hx
    omega
  · have hy := congrArg Prod.snd he
    dsimp [PrimitiveCode.world] at hy
    omega

/-- Initial strips use their working lanes, and every later arm stays outside the core window. -/
private theorem core_cell_arm_wall_clear (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (a : Cell ((PrimitiveCode.core g).instanceOf w hw).width ((PrimitiveCode.core g).instanceOf w hw).height)
    (hlane : ∀ role, Outward (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) 0)
      ((PrimitiveCode.core g).world w hw a) →
      SameLane (PortAnnulus.innerDirection role)
        (Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) 0)
        ((PrimitiveCode.core g).world w hw a))
    (role : Fin 3) (c : PrimitiveCode) (hc : c ∈ (armSpec w g role).codes)
    (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height) (hp : p ∈ (c.instanceOf w hw).board.walls) :
    (PrimitiveCode.core g).world w hw a ≠ c.world w hw p := by
  let P := armSpec w g role
  have G : P.Geometry w := armSpec_geometry w g role
  change c ∈ P.codes at hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases (P.mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · by_cases hz : i = 0
    · subst i
      obtain ⟨ho,_,hn⟩ := line_wall_envelope w hw _ (P.line_good w G 0 hi') p hp
      change Outward _ (Line.along w _ ((armSpec w g role).line 0).segment.start 0) _ at ho
      rw [armSpec_first_direction,armSpec_first_start] at ho hn
      intro he
      rw [←he] at ho hn
      exact hn (hlane role ho)
    · obtain ⟨u,hu,ha⟩ := P.line_wall_at w hw G i hi' p hp
      exact Ne.symm (core_tail_ne w hw g role (w+1) (by unfold origin; omega)
        ⟨_,P.segment_mem_tail i hi' (by omega),hu⟩ ha a)
  · have ha := P.turn_wall_at w hw i p
    rw [P.join_eq w G i ht.1] at ha
    exact Ne.symm (core_tail_ne w hw g role (FiniteTools.radius w)
      (by unfold origin FiniteTools.radius; omega)
      ⟨_,P.segment_mem_tail (i+1) ht.1 (by omega),P.start_contains w G (i+1) ht.1⟩ ha a)

theorem core_cell_gate_wall_clear (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (a : Cell ((PrimitiveCode.core g).instanceOf w hw).width ((PrimitiveCode.core g).instanceOf w hw).height)
    (hfloor : a ∉ ((PrimitiveCode.core g).instanceOf w hw).board.walls)
    (hlane : ∀ role, Outward (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) 0)
      ((PrimitiveCode.core g).world w hw a) →
      SameLane (PortAnnulus.innerDirection role)
        (Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) 0)
        ((PrimitiveCode.core g).world w hw a))
    (c : PrimitiveCode) (hc : c ∈ gateCodes w g)
    (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height) (hp : p ∈ (c.instanceOf w hw).board.walls) :
    (PrimitiveCode.core g).world w hw a ≠ c.world w hw p := by
  rw [gateCodes_eq_specs] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · intro he
    exact hfloor (world_injective w hw (.core g) he ▸ hp)
  · obtain ⟨role,_,hc⟩ := List.mem_flatMap.mp hc
    exact core_cell_arm_wall_clear w hw g a hlane role c hc p hp

theorem PathSpec.core_not_mem (P : PathSpec) (g : GateTileState) : .core g ∉ P.codes := by
  intro hc
  obtain ⟨i,_,hc⟩ := List.mem_flatMap.mp hc
  rcases (P.mem_block i (.core g)).mp hc with h | ⟨_,h⟩ <;> cases h

theorem gate_core_origin (w : ℕ) (g h : GateTileState) (hc : .core g ∈ gateCodes w h) : g = h := by
  rw [gateCodes_eq_specs] at hc
  rcases List.mem_cons.mp hc with he | hc
  · exact PrimitiveCode.core.inj he
  · obtain ⟨role,_,hc⟩ := List.mem_flatMap.mp hc
    exact ((armSpec w h role).core_not_mem g hc).elim

def andPortSupportIndex (w : ℕ) (role : Fin 3) : Fin (andTravel (andPortLabel w role)+3) :=
  ⟨if role = 2 then 0 else 3,by fin_cases role <;> simp [andPortLabel,andTravel]⟩

def orPortSupportIndex (role : Fin 3) : Fin 4 := ⟨if role = 2 then 0 else 3,by split <;> omega⟩

theorem andPortSupport_world (w : ℕ) (hw : 2 ≤ w) (role : Fin 3) :
    coreWorld w (andLine w (andPortLabel w role) (andPortSupportIndex w role)) =
      Line.along w (PortAnnulus.innerDirection role).opposite (corePort w true role) 1 := by
  fin_cases role <;> apply Prod.ext <;>
    simp [andPortSupportIndex,andLine,andLinePoint,andPortLabel,andVertical,andTravel,
      andPoint,coreWorld,corePort,PortAnnulus.innerDirection,Line.along,Direction.opposite,
      origin,coreOffset,padding,spacing] <;> omega

theorem orPortSupport_world (w : ℕ) (hw : 2 ≤ w) (role : Fin 3) :
    coreWorld w (orLine w (orPortLabel w role) (orPortSupportIndex role)) =
      Line.along w (PortAnnulus.innerDirection role).opposite (corePort w false role) 1 := by
  fin_cases role <;> apply Prod.ext <;>
    simp [orPortSupportIndex,orLine,orLinePoint,orPortLabel,orVertical,orPoint,coreWorld,
      corePort,PortAnnulus.innerDirection,Line.along,Direction.opposite,
      origin,coreOffset,padding,spacing] <;> omega

set_option maxHeartbeats 1000000 in
theorem andFullRail_outward_lane (w : ℕ) (hw : 2 ≤ w) (role : Fin 3)
    (r : FiniteCoreRails.AndRail) (i : Fin (r.count w))
    (h : Outward (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w true role) 0)
      (coreWorld w (r.cell w i))) :
    SameLane (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w true role) 0)
      (coreWorld w (r.cell w i)) := by
  have hi := i.isLt
  fin_cases role <;> cases r <;>
    simp [Outward,SameLane,PortAnnulus.innerDirection,Line.along,corePort,coreWorld,
      FiniteCoreRails.AndRail.cell,FiniteCoreRails.AndRail.point,FiniteCoreRails.AndRail.count,
      origin,coreOffset,padding,spacing] at * <;> omega

set_option maxHeartbeats 1000000 in
theorem orFullRail_outward_lane (w : ℕ) (hw : 2 ≤ w) (role : Fin 3)
    (r : FiniteCoreRails.OrRail) (i : Fin (r.count w))
    (h : Outward (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w false role) 0)
      (coreWorld w (r.cell w i))) :
    SameLane (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w false role) 0)
      (coreWorld w (r.cell w i)) := by
  have hi := i.isLt
  fin_cases role <;> cases r <;>
    simp [Outward,SameLane,PortAnnulus.innerDirection,Line.along,corePort,coreWorld,
      FiniteCoreRails.OrRail.cell,FiniteCoreRails.OrRail.point,FiniteCoreRails.OrRail.count,
      origin,coreOffset,padding,spacing] at * <;> omega

end PushPuzzle.PushS.FiniteRouting
