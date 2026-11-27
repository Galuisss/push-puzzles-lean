/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateActiveRegion
public import PushS.FiniteCoreRailFloor

/-! Every literal core-envelope floor cell avoids the complete actual local gate wall union. -/

public section
namespace PushPuzzle.PushS.FiniteGateActiveRegion

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteCoreGuardCoverage

attribute [local irreducible] FiniteGeometry.side Line.width Line.height Line.walls FiniteTools.side

/-- The uniform core cell as a cell of its actual emitted AND/OR primitive instance. -/
def coreCell (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) :
    Cell ((PrimitiveCode.core g).instanceOf w hw).width ((PrimitiveCode.core g).instanceOf w hw).height := by
  rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
  cases kind <;> exact p

theorem coreCell_world (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) :
    (PrimitiveCode.core g).world w hw (coreCell w hw g p) = coreWorld w p := by
  rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
  cases kind <;> rfl

private theorem coreCell_wall (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) :
    coreCell w hw g p ∈ ((PrimitiveCode.core g).instanceOf w hw).board.walls ↔ p ∈ walls w g.core.isAND := by
  rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
  cases kind <;> rfl

/-- An emitted arm instruction is one indexed line or one protected turn. -/
theorem arm_code_cases (w : ℕ) (g : GateTileState) (role : Fin 3) (c : PrimitiveCode)
    (hc : c ∈ (armSpec w g role).codes) :
    (∃ i, i < (armSpec w g role).segments.length ∧ c = .line ((armSpec w g role).line i)) ∨
      (∃ i, (armSpec w g role).hasTurn i ∧ c = .turn ((armSpec w g role).turn i)) := by
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases ((armSpec w g role).mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · exact Or.inl ⟨i,hi',rfl⟩
  · exact Or.inr ⟨i,ht,rfl⟩

/-- Every actual arm wall avoids each core-envelope cell that is real core floor. -/
private theorem core_arm_wall_clear (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (a : Cell (FiniteGeometry.side w) (FiniteGeometry.side w))
    (henv : Envelope w g.core.isAND (coordinates a)) (hfloor : a ∉ walls w g.core.isAND)
    (role : Fin 3) (c : PrimitiveCode) (hc : c ∈ (armSpec w g role).codes)
    (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height) (hp : p ∈ (c.instanceOf w hw).board.walls) :
    coreWorld w a ≠ c.world w hw p := by
  let P := armSpec w g role
  have G := armSpec_geometry w g role
  rcases arm_code_cases w g role c hc with ⟨i,hi',rfl⟩ | ⟨i,ht,rfl⟩
  · by_cases hz : i = 0
    · subst i
      apply Ne.symm
      exact initial_code_wall_ne_floor w hw g.core.isAND role (P.line 0) (P.line_good w G 0 hi')
        (armSpec_first_start w g role) (armSpec_first_direction w g role) rfl p hp a henv hfloor
    · obtain ⟨u,hu,ha⟩ := P.line_wall_at w hw G i hi' p hp
      have hh := core_tail_ne w hw g role (w+1) (by unfold origin; omega)
        ⟨_,P.segment_mem_tail i hi' (by omega),hu⟩ ha (coreCell w hw g a)
      simpa only [coreCell_world] using Ne.symm hh
  · have ha := P.turn_wall_at w hw i p
    rw [P.join_eq w G i ht.1] at ha
    have hh := core_tail_ne w hw g role (FiniteTools.radius w)
      (by unfold origin FiniteTools.radius; omega)
      ⟨_,P.segment_mem_tail (i+1) ht.1 (by omega),P.start_contains w G (i+1) ht.1⟩ ha (coreCell w hw g a)
    simpa only [coreCell_world] using Ne.symm hh

/-- The complete actual gate-code table leaves every real core-envelope floor cell clear. -/
theorem core_gate_wall_clear (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (a : Cell (FiniteGeometry.side w) (FiniteGeometry.side w))
    (henv : Envelope w g.core.isAND (coordinates a)) (hfloor : a ∉ walls w g.core.isAND)
    (c : PrimitiveCode) (hc : c ∈ gateCodes w g)
    (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height) (hp : p ∈ (c.instanceOf w hw).board.walls) :
    coreWorld w a ≠ c.world w hw p := by
  rw [gateCodes_eq_specs] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · intro he
    have hh : coreCell w hw g a = p :=
      PrimitiveCode.world_injective w hw (.core g) ((coreCell_world w hw g a).trans he)
    exact hfloor ((coreCell_wall w hw g a).mp (hh.symm ▸ hp))
  · obtain ⟨role,_,hc⟩ := List.mem_flatMap.mp hc
    exact core_arm_wall_clear w hw g a henv hfloor role c hc p hp

end PushPuzzle.PushS.FiniteGateActiveRegion
