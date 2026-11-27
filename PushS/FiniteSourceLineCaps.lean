/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceBoundarySupports
public import PushS.FiniteSourceTurnCenters

/-! Actual line end supports are floor at collinear joins, turns, and source-grid ports. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem path_after_cap_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point)
    (P : PathSpec) (G : P.Geometry w)
    (hm : ∀ c ∈ P.codes, (pos,c) ∈ codes w v) (i : ℕ) (hi : i+1 < P.segments.length)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos ((P.line i).capWorld w hw false)) :
    q ∉ (inventory w hw v).walls := by
  by_cases ht : P.hasTurn i
  · have H := P.junction_contract w G i ht
    apply center_floor w hw v pos (P.turn i) (hm _ (P.turn_mem_codes i ht)) q
    exact hq.trans (congrArg (macroShift w pos) (H.incoming_after_cap w hw))
  · have H := P.collinear_contract w G i hi ht
    apply row_floor w hw v pos (P.line (i+1)) (hm _ (P.line_mem_codes (i+1) hi))
      H.next_good 2 (by have h := H.next_good.2.1; omega) q
    rw [LineCode.rowWorld_eq]
    have he := H.after_cap_neighbor_rail w hw
    rw [LineCode.railPoint_world] at he
    exact hq.trans (congrArg (macroShift w pos) he)

private theorem gate_last_cap (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3) :
    (gatePortLine w g role).capWorld w hw false =
      boundaryCap w (PortAnnulus.outerDirection (g.pattern,g.rotation,role)) (g.incoming.get role) := by
  rw [LineCode.capWorld_eq w hw _ (gatePortLine_good w g role)]
  change Line.along w (segmentDirection ((armSpec w g role).line ((armRoute w g role).length-1)).segment)
    ((armSpec w g role).line ((armRoute w g role).length-1)).segment.finish 2 = _
  rw [armSpec_last_direction,armSpec_last_finish]
  cases g.incoming.get role <;> simp [boundaryCap,advance_zero]

private theorem wire_last_cap (w : ℕ) (hw : 2 ≤ w) (a : Gadgets.Wires.Catalog.Bitmap.Args)
    (i : ℕ) (hi : i+1 = (wireRoute w a.1).length) :
    ((wireSpec w a).line i).capWorld w hw false = boundaryCap w (Gadgets.Wires.Catalog.targetDirection a.1) false := by
  have hgood := (wireSpec w a).line_good w (wireSpec_geometry w a) i (by change i < (wireRoute w a.1).length; omega)
  rw [LineCode.capWorld_eq w hw _ hgood]
  simp only [Bool.false_eq_true,↓reduceIte,wire_last_direction w a i hi,wire_last_finish w a i hi]
  rfl

theorem line_after_cap_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (pos : GridRouting.Point) (c : LineCode) (hc : (pos,PrimitiveCode.line c) ∈ codes w v)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos (c.capWorld w hw false)) :
    q ∉ (inventory w hw v).walls := by
  have hcl := code_local w v (pos,.line c) hc
  cases hcode : CellPlan.cell (v,pos) with
  | none => simp only [hcode,localCodes] at hcl; simp at hcl
  | some code =>
    cases code with
    | inl g =>
      have hcg : .line c ∈ gateCodes w g.2 := by simpa [hcode,localCodes] using hcl
      obtain ⟨role,i,hi,rfl⟩ := gate_line_origin w g.2 c hcg
      let P := armSpec w g.2 role
      have hm : ∀ d ∈ P.codes, (pos,d) ∈ codes w v := by
        intro d hd
        apply code_mem_of_local w v pos d
        simpa [hcode,localCodes] using arm_code_mem_gateCodes w g.2 role d hd
      by_cases hn : i+1 < (armRoute w g.2 role).length
      · exact path_after_cap_floor w hw v pos P (armSpec_geometry w g.2 role) hm i hn q hq
      · have he : i = (armRoute w g.2 role).length-1 := by omega
        subst i
        have hport : LocalPort (CellPlan.cell (v,pos)) (PortAnnulus.outerDirection (g.2.pattern,g.2.rotation,role)) (g.2.incoming.get role) := by
          rw [hcode]
          exact ⟨role,rfl,rfl⟩
        exact port_cap_floor w hw v hP hT pos _ _ hport q
          (hq.trans (congrArg (macroShift w pos) (gate_last_cap w hw g.2 role)))
    | inr a =>
      have hcw : .line c ∈ wireCodes w a.2 := by simpa [hcode,localCodes] using hcl
      obtain ⟨i,hi,rfl⟩ := (wireSpec w a.2).line_code_origin c hcw
      change i < (wireRoute w a.2.1).length at hi
      let P := wireSpec w a.2
      have hm : ∀ d ∈ P.codes, (pos,d) ∈ codes w v := by
        intro d hd
        apply code_mem_of_local w v pos d
        change d ∈ wireCodes w a.2 at hd
        simpa [hcode,localCodes] using hd
      by_cases hn : i+1 < (wireRoute w a.2.1).length
      · exact path_after_cap_floor w hw v pos P (wireSpec_geometry w a.2) hm i hn q hq
      · have he : i+1 = (wireRoute w a.2.1).length := by omega
        have hport : LocalPort (CellPlan.cell (v,pos)) (Gadgets.Wires.Catalog.targetDirection a.2.1) false := by
          rw [hcode]
          exact Or.inr ⟨rfl,rfl⟩
        exact port_cap_floor w hw v hP hT pos _ false hport q
          (hq.trans (congrArg (macroShift w pos) (wire_last_cap w hw a.2 i he)))

end PushPuzzle.PushS.FiniteSourceInventory
