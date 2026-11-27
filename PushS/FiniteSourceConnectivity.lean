/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceLineConnectivity
public import PushS.FiniteSourceTurnConnectivity
public import PushS.FiniteSourceCoreConnectivity
public import PushS.FiniteSourceLegal

/-! Every literal global inventory identity has connected source and target slots; the actual board satisfies C1. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem primitiveLabel_surjective (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (i : Fin (codes w v).length) (c : PrimitiveCode) (hc : ((codes w v).get i).2 = c)
    (l : (inventory w hw v).PhysicalLabel) (hi : l.1 = i) :
    ∃ q, primitiveLabel w hw v i c hc q = l := by
  subst c
  rcases l with ⟨j,l⟩
  dsimp at hi
  subst j
  exact ⟨l,rfl⟩

theorem turnCode_perpendicular (w : ℕ) (v : CellPlan.Source)
    (i : Fin (codes w v).length) (c : TurnCode) (hc : ((codes w v).get i).2 = .turn c) :
    Perpendicular c.incoming c.outgoing := by
  have hm : (((codes w v).get i).1,PrimitiveCode.turn c) ∈ codes w v := by
    have he : (codes w v).get i = (((codes w v).get i).1,PrimitiveCode.turn c) := Prod.ext rfl hc
    exact he ▸ List.get_mem (codes w v) i
  have hl := code_local w v _ hm
  change PrimitiveCode.turn c ∈ localCodes w (CellPlan.cell (v,((codes w v).get i).1)) at hl
  cases hcode : CellPlan.cell (v,((codes w v).get i).1) with
  | none => rw [hcode] at hl; simp [localCodes] at hl
  | some code =>
    rw [hcode] at hl
    cases code with
    | inl g =>
      have hm : .turn c ∈ gateCodes w g.2 := hl
      obtain ⟨role,j,hj,rfl⟩ := gate_turn_origin w g.2 c hm
      exact (armSpec w g.2 role).turn_perpendicular w (armSpec_geometry w g.2 role) j hj
    | inr a =>
      have hm : .turn c ∈ wireCodes w a.2 := hl
      obtain ⟨j,hj,rfl⟩ := (wireSpec w a.2).turn_code_origin c hm
      exact (wireSpec w a.2).turn_perpendicular w (wireSpec_geometry w a.2) j hj

/-- All actual source and target boxes remain in the same displacement component of the complete wall union. -/
theorem connected (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (l : (inventory w hw v).PhysicalLabel) :
    SameComponent (inventory w hw v).board ((inventory w hw v).source l) ((inventory w hw v).target l) := by
  cases he : ((codes w v).get l.1).2 with
  | core g =>
    let s : CoreSite w hw v := ⟨l.1,g,he⟩
    exact s.owner_connected l rfl
  | line c =>
    let s : LineSite w hw v := ⟨l.1,c,he⟩
    obtain ⟨q,hq⟩ := primitiveLabel_surjective w hw v l.1 (.line c) he l rfl
    have hs : s.label q = l := hq
    rw [←hs]
    exact s.source_target_connected hP hT q
  | turn c =>
    let s : TurnSite w hw v := ⟨l.1,c,he,turnCode_perpendicular w v l.1 c he⟩
    obtain ⟨q,hq⟩ := primitiveLabel_surjective w hw v l.1 (.turn c) he l rfl
    have hs : s.label q = l := hq
    rw [←hs]
    exact s.source_target_connected q

/-- The complete actual emitted puzzle has a physical identity for every box and target. -/
def slotMatching (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    SlotMatching (checkedPuzzle w hw v hP hT) (inventory w hw v).PhysicalLabel :=
  (inventory w hw v).slotMatching (admissible w hw v hP hT) (connected w hw v hP hT)

/-- C1 holds for the literal box and goal sets of the complete actual source board. -/
theorem componentBalanced (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    ComponentBalanced (checkedPuzzle w hw v hP hT).board (checkedPuzzle w hw v hP hT).initial :=
  (slotMatching w hw v hP hT).componentBalanced

end PushPuzzle.PushS.FiniteSourceInventory
