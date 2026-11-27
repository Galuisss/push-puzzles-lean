/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingTurnSupports
public import PushS.FiniteSourceLineConnectivity
public import PushS.FiniteSourceTurnGlyph

/-! Both normal slots of every actual turn label have a literal global displacement-SCC path. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem path_turn_ray_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point)
    (P : PathSpec) (G : P.Geometry w) (hm : ∀ c ∈ P.codes, (pos,c) ∈ codes w v)
    (i : ℕ) (hi : P.hasTurn i) (incoming : Bool) (n : ℕ) (hn : n ≤ 3)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos
      (Line.along w (if incoming then (P.turn i).incoming.opposite else (P.turn i).outgoing) (P.turn i).corner n)) :
    q ∉ (inventory w hw v).walls := by
  by_cases hz : n = 0
  · subst n
    apply center_floor w hw v pos (P.turn i) (hm _ (P.turn_mem_codes i hi)) q
    rw [TurnCode.centerWorld_eq,←Line.along_zero w (if incoming then (P.turn i).incoming.opposite else (P.turn i).outgoing)]
    exact hq
  · have H := P.junction_contract w G i hi
    cases incoming
    · apply row_floor w hw v pos (P.line (i+1)) (hm _ (P.line_mem_codes (i+1) hi.1)) H.outgoing_good
        (n-1) (by have h := H.outgoing_good.2.1; omega) q
      have he := LineCode.outgoing_row_ray w hw (P.line (i+1)) (P.turn i) H.outgoing_good
        H.outgoing_direction H.outgoing_start (n-1) (by have h := H.outgoing_good.2.1; omega)
      have hnat : n-1+1 = n := by omega
      rw [hnat] at he
      exact hq.trans (congrArg (macroShift w pos) he.symm)
    · let len := segmentLength (P.line i).segment
      have hl := H.incoming_good.2.1
      have hn' : len+2-n ≤ len+1 := by dsimp [len]; omega
      apply row_floor w hw v pos (P.line i) (hm _ (P.line_mem_codes i (by have h := hi.1; omega))) H.incoming_good
        (len+2-n) hn' q
      have he := LineCode.incoming_row_ray w hw (P.line i) (P.turn i) H.incoming_good
        H.incoming_direction H.incoming_finish (len+2-n) hn'
      have hnat : segmentLength (P.line i).segment+2-(len+2-n) = n := by dsimp [len]; omega
      rw [hnat] at he
      exact hq.trans (congrArg (macroShift w pos) he.symm)

private theorem turn_ray_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point) (c : TurnCode) (hc : (pos,PrimitiveCode.turn c) ∈ codes w v)
    (incoming : Bool) (n : ℕ) (hn : n ≤ 3) (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos
      (Line.along w (if incoming then c.incoming.opposite else c.outgoing) c.corner n)) :
    q ∉ (inventory w hw v).walls := by
  have hcl := code_local w v (pos,.turn c) hc
  cases hcode : CellPlan.cell (v,pos) with
  | none => simp [hcode,localCodes] at hcl
  | some code =>
    cases code with
    | inl g =>
      have hcg : .turn c ∈ gateCodes w g.2 := by simpa [hcode,localCodes] using hcl
      obtain ⟨role,i,hi,rfl⟩ := gate_turn_origin w g.2 c hcg
      apply path_turn_ray_floor w hw v pos (armSpec w g.2 role) (armSpec_geometry w g.2 role) _ i hi incoming n hn q hq
      intro d hd
      apply code_mem_of_local w v pos d
      simpa [hcode,localCodes] using arm_code_mem_gateCodes w g.2 role d hd
    | inr a =>
      have hcw : .turn c ∈ wireCodes w a.2 := by simpa [hcode,localCodes] using hcl
      obtain ⟨i,hi,rfl⟩ := (wireSpec w a.2).turn_code_origin c hcw
      apply path_turn_ray_floor w hw v pos (wireSpec w a.2) (wireSpec_geometry w a.2) _ i hi incoming n hn q hq
      intro d hd
      apply code_mem_of_local w v pos d
      change d ∈ wireCodes w a.2 at hd
      simpa [hcode,localCodes] using hd

namespace TurnSite

variable {w hw v} (s : TurnSite w hw v)

theorem code_mem : (((codes w v).get s.index).1,PrimitiveCode.turn s.code) ∈ codes w v := by
  have h := List.get_mem (codes w v) s.index
  have he : (((codes w v).get s.index).1,PrimitiveCode.turn s.code) = (codes w v).get s.index :=
    Prod.ext rfl s.code_eq.symm
  exact he ▸ h

theorem actual_cell_coordinates (p : Cell (FiniteTools.side w) (FiniteTools.side w)) :
    coordinates (s.actualEmbedding.cells p) = macroShift w ((codes w v).get s.index).1
      ((PrimitiveCode.turn s.code).world w hw ((Turn.orientation w s.code.incoming s.code.outgoing).cells p)) := by
  change coordinates ((primitiveEmbedding w hw v s.index (.turn s.code) s.code_eq).cells
    ((Turn.orientation w s.code.incoming s.code.outgoing).cells p)) = _
  rw [primitiveEmbedding_coordinates w hw v s.index (.turn s.code) s.code_eq
    ((Turn.orientation w s.code.incoming s.code.outgoing).cells p)]
  have hx : s.dx = tileStride w*((codes w v).get s.index).1.1+PrimitiveCode.offsetX w (.turn s.code) := by
    change tileStride w*((codes w v).get s.index).1.1+PrimitiveCode.offsetX w ((codes w v).get s.index).2 = _
    rw [s.code_eq]
  have hy : s.dy = tileStride w*((codes w v).get s.index).1.2+PrimitiveCode.offsetY w (.turn s.code) := by
    change tileStride w*((codes w v).get s.index).1.2+PrimitiveCode.offsetY w ((codes w v).get s.index).2 = _
    rw [s.code_eq]
  change shiftPoint s.dx s.dy (coordinates ((Turn.orientation w s.code.incoming s.code.outgoing).cells p)) = _
  rw [hx,hy]
  simp only [PrimitiveCode.world,macroShift,shiftPoint,coordinates,Nat.add_assoc]

private theorem support_floor (role : Fin 2) (i : Fin 4) :
    s.actualEmbedding.cells (Turn.support w role i) ∉ (inventory w hw v).walls := by
  apply turn_ray_floor w hw v _ s.code s.code_mem (role = 0) (if role = 0 then 3-i.val else i.val)
    (by split_ifs <;> have h := i.isLt <;> omega)
  rw [s.actual_cell_coordinates]
  change macroShift w ((codes w v).get s.index).1 (s.code.supportWorld w hw role i) = _
  rw [TurnCode.supportWorld_eq w hw s.code s.perpendicular]
  by_cases h : role = 0 <;> simp [h]

theorem normal_connected (a b : Bool) (role : Fin 2) :
    SameComponent (inventory w hw v).board
      (s.actualEmbedding.cells (Turn.cell w a role)) (s.actualEmbedding.cells (Turn.cell w b role)) := by
  have hh := sameComponent_line (n := 1) (B := (inventory w hw v).board)
    (fun i => s.actualEmbedding.cells (Turn.support w role i)) (s.support_floor role)
    (fun i => s.actualEmbedding.adjacent _ _ _ (Turn.support_adjacent w role i))
    (Turn.supportIndex a) (Turn.supportIndex b)
    (by dsimp [Turn.supportIndex]; have h := Bool.toNat_le a; omega)
    (by dsimp [Turn.supportIndex]; have h := Bool.toNat_le b; omega)
  simpa only [Turn.support_slot] using hh

theorem source_target_connected (role : Fin 2) :
    SameComponent (inventory w hw v).board ((inventory w hw v).source (s.label role)) ((inventory w hw v).target (s.label role)) := by
  rw [s.source_actual,s.target_actual]
  exact s.normal_connected _ _ role

end TurnSite
end PushPuzzle.PushS.FiniteSourceInventory
