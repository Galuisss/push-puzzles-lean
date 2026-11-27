/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceLineCaps
public import PushS.FiniteSourceCoreRailFloor

/-! Literal first supports of all actual compiled lines, including core and source-grid seams. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem path_before_cap_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point)
    (P : PathSpec) (G : P.Geometry w)
    (hm : ∀ c ∈ P.codes, (pos,c) ∈ codes w v) (i : ℕ) (hi : i < P.segments.length) (hi0 : 0 < i)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos ((P.line i).capWorld w hw true)) :
    q ∉ (inventory w hw v).walls := by
  let j := i-1
  have he : j+1 = i := by dsimp [j]; omega
  have hj : j+1 < P.segments.length := by omega
  by_cases ht : P.hasTurn j
  · have H := P.junction_contract w G j ht
    apply center_floor w hw v pos (P.turn j) (hm _ (P.turn_mem_codes j ht)) q
    have hs := H.outgoing_before_cap w hw
    rw [he] at hs
    exact hq.trans (congrArg (macroShift w pos) hs)
  · have H := P.collinear_contract w G j hj ht
    apply row_floor w hw v pos (P.line j) (hm _ (P.line_mem_codes j (by omega))) H.first_good
      (segmentLength (P.line j).segment-1) (by omega) q
    rw [LineCode.rowWorld_eq]
    have hs := H.before_cap_neighbor_rail w hw
    rw [LineCode.railPoint_world] at hs
    rw [he] at hs
    exact hq.trans (congrArg (macroShift w pos) hs)

private theorem wire_first_cap (w : ℕ) (hw : 2 ≤ w) (a : Gadgets.Wires.Catalog.Bitmap.Args) :
    ((wireSpec w a).line 0).capWorld w hw true = boundaryCap w (Gadgets.Wires.Catalog.sourceDirection a.1).opposite true := by
  have hi : 0 < (wireRoute w a.1).length := by rw [wireRoute_length]; split_ifs <;> decide
  have hgood := (wireSpec w a).line_good w (wireSpec_geometry w a) 0 hi
  rw [LineCode.capWorld_eq w hw _ hgood]
  simp only [↓reduceIte,wire_first_direction,wire_first_start]
  cases hd : Gadgets.Wires.Catalog.sourceDirection a.1 <;>
    dsimp [boundaryCap,boundaryPoint,Line.along,FiniteRouting.advance,Direction.opposite] <;>
    apply Prod.ext <;> simp only [tileStride,spacing,padding] <;> omega

private theorem gate_first_cap (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3) :
    ((armSpec w g role).line 0).capWorld w hw true =
      Line.along w (PortAnnulus.innerDirection role).opposite (corePort w g.core.isAND role) 1 := by
  have hi : 0 < (armRoute w g role).length := by rw [armRoute_length,route_length]; omega
  rw [LineCode.capWorld_eq w hw _ ((armSpec w g role).line_good w (armSpec_geometry w g role) 0 hi)]
  simp only [↓reduceIte,armSpec_first_direction,armSpec_first_start]

theorem line_before_cap_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (pos : GridRouting.Point) (c : LineCode) (hc : (pos,PrimitiveCode.line c) ∈ codes w v)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos (c.capWorld w hw true)) :
    q ∉ (inventory w hw v).walls := by
  have hcl := code_local w v (pos,.line c) hc
  cases hcode : CellPlan.cell (v,pos) with
  | none => simp [hcode,localCodes] at hcl
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
      by_cases hz : i = 0
      · subst i
        have hcore : (pos,PrimitiveCode.core g.2) ∈ codes w v := by
          apply code_mem_of_local w v pos (.core g.2)
          simp [hcode,localCodes,gateCodes]
        exact core_port_support_floor w hw v pos g.2 hcore role q
          (hq.trans (congrArg (macroShift w pos) (gate_first_cap w hw g.2 role)))
      · exact path_before_cap_floor w hw v pos P (armSpec_geometry w g.2 role) hm i hi (by omega) q hq
    | inr a =>
      have hcw : .line c ∈ wireCodes w a.2 := by simpa [hcode,localCodes] using hcl
      obtain ⟨i,hi,rfl⟩ := (wireSpec w a.2).line_code_origin c hcw
      let P := wireSpec w a.2
      have hm : ∀ d ∈ P.codes, (pos,d) ∈ codes w v := by
        intro d hd
        apply code_mem_of_local w v pos d
        change d ∈ wireCodes w a.2 at hd
        simpa [hcode,localCodes] using hd
      by_cases hz : i = 0
      · subst i
        have hport : LocalPort (CellPlan.cell (v,pos)) (Gadgets.Wires.Catalog.sourceDirection a.2.1).opposite true := by
          rw [hcode]
          exact Or.inl ⟨rfl,rfl⟩
        exact port_cap_floor w hw v hP hT pos _ true hport q
          (hq.trans (congrArg (macroShift w pos) (wire_first_cap w hw a.2)))
      · exact path_before_cap_floor w hw v pos P (wireSpec_geometry w a.2) hm i hi (by omega) q hq

end PushPuzzle.PushS.FiniteSourceInventory
