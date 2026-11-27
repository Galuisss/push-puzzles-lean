/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceLineCaps
public import PushS.FiniteSourceLineGlyph

/-! Actual line normal slots lie in one global displacement SCC, including unchanged-phase labels. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory.LineSite

open PushFS PushFS.Reduction FiniteRouting

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

theorem code_mem : (((codes w v).get s.index).1,PrimitiveCode.line s.code) ∈ codes w v := by
  have h := List.get_mem (codes w v) s.index
  have he : (((codes w v).get s.index).1,PrimitiveCode.line s.code) = (codes w v).get s.index :=
    Prod.ext rfl s.code_eq.symm
  exact he ▸ h

theorem good : LineGood w s.code.segment :=
  (local_line_good w _ s.code (code_local w v _ s.code_mem)).1

theorem first_false : s.code.first = false :=
  (local_line_good w _ s.code (code_local w v _ s.code_mem)).2

theorem actual_cell_coordinates (p : Cell (Line.width w s.atoms) (Line.height w)) :
    coordinates (s.actualEmbedding.cells p) = macroShift w ((codes w v).get s.index).1
      ((PrimitiveCode.line s.code).world w hw ((Line.rotation w s.atoms (segmentDirection s.code.segment)).cells p)) := by
  change coordinates ((primitiveEmbedding w hw v s.index (.line s.code) s.code_eq).cells
    ((Line.rotation w s.atoms (segmentDirection s.code.segment)).cells p)) = _
  rw [primitiveEmbedding_coordinates w hw v s.index (.line s.code) s.code_eq
    ((Line.rotation w s.atoms (segmentDirection s.code.segment)).cells p)]
  change shiftPoint s.dx s.dy (coordinates ((Line.rotation w s.atoms (segmentDirection s.code.segment)).cells p)) = _
  rw [s.dx_eq,s.dy_eq]
  simp only [PrimitiveCode.world,macroShift,shiftPoint,coordinates,Nat.add_assoc]

def shortRail (i : Fin (Line.span w s.atoms+3)) : Cell (width w v) (height w v) :=
  s.actualEmbedding.cells (Line.Readout.rail w s.atoms ⟨i.val+1,by have h := i.isLt; omega⟩)

private theorem shortRail_floor (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (i : Fin (Line.span w s.atoms+3)) : s.shortRail i ∉ (inventory w hw v).walls := by
  have hspan : Line.span w s.atoms = segmentLength s.code.segment := Line.program_span_of_bound w _ _ s.good.2.1
  by_cases hi : i.val ≤ Line.span w s.atoms+1
  · apply row_floor w hw v _ s.code s.code_mem s.good i.val (by omega) (s.shortRail i)
    have hr : Line.Readout.rail w s.atoms ⟨i.val+1,by have h := i.isLt; omega⟩ =
        (Line.railEmbedding w s.atoms).cells (⟨i.val,by omega⟩,Line.railRow w) := by
      apply Prod.ext <;> apply Fin.ext
      · dsimp [Line.Readout.rail,Line.railEmbedding,GridEmbedding.translate]
        unfold FiniteTools.radius
        omega
      · dsimp [Line.Readout.rail,Line.railEmbedding,GridEmbedding.translate,Line.railRow,Line.workY]
        omega
    rw [shortRail,s.actual_cell_coordinates,hr]
    rfl
  · have he : i.val+1 = Line.span w s.atoms+3 := by have h := i.isLt; omega
    apply line_after_cap_floor w hw v hP hT _ s.code s.code_mem (s.shortRail i)
    rw [shortRail,s.actual_cell_coordinates]
    unfold LineCode.capWorld LineCode.capSlot
    simp only [LineCode.capIndex,Bool.false_eq_true,↓reduceIte]
    congr 4
    exact Fin.ext he

private theorem shortRail_adjacent (i : Fin (Line.span w s.atoms+2)) :
    Adjacent (s.actualEmbedding.direction .east) (s.shortRail i.castSucc) (s.shortRail i.succ) := by
  apply s.actualEmbedding.adjacent .east
  dsimp [Line.Readout.rail,Adjacent]
  exact ⟨by omega,rfl⟩

def shortIndex (phase : Bool) (l : (PrimitiveCode.line s.code).Labels w) : Fin (Line.span w s.atoms+3) :=
  ⟨Line.position w s.atoms phase l.val,by
    have hb := Line.positions_bounds w hw phase s.atoms (Line.position_mem w s.atoms phase l.val)
    have hphase := Bool.toNat_le phase
    omega⟩

private theorem shortIndex_interior (phase : Bool) (l : (PrimitiveCode.line s.code).Labels w) :
    0 < (s.shortIndex phase l).val ∧ (s.shortIndex phase l).val ≤ Line.span w s.atoms+1 := by
  have hb := Line.positions_bounds w hw phase s.atoms (Line.position_mem w s.atoms phase l.val)
  have hp := Bool.toNat_le phase
  have hf := s.first_false
  let l' : Line.OwnedLabel w s.atoms false s.code.last := ⟨l.val,by simpa only [hf,atoms] using l.property⟩
  have ha := Line.owned_position_after_first w (segmentLength s.code.segment) hw (s.code.above != s.code.desiredSide) phase s.code.last l'
  change phase.toNat+2 ≤ Line.position w s.atoms phase l.val at ha
  dsimp [shortIndex]
  omega

private theorem shortRail_slot (phase : Bool) (l : (PrimitiveCode.line s.code).Labels w) :
    s.shortRail (s.shortIndex phase l) = s.actualEmbedding.cells (Line.cell w hw s.atoms phase l.val) := by
  change Line.OwnedLabel w s.atoms s.code.first s.code.last at l
  change s.actualEmbedding.cells (Line.Readout.rail w s.atoms (Line.Readout.railIndex w hw s.atoms phase l.val)) = _
  rw [Line.Readout.rail_slot]

private theorem normal_connected (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (a b : Bool) (l : (PrimitiveCode.line s.code).Labels w) :
    SameComponent (inventory w hw v).board
      (s.actualEmbedding.cells (Line.cell w hw s.atoms a l.val))
      (s.actualEmbedding.cells (Line.cell w hw s.atoms b l.val)) := by
  have hh := sameComponent_line (n := Line.span w s.atoms)
    (B := (inventory w hw v).board) s.shortRail (s.shortRail_floor hP hT) s.shortRail_adjacent
    (s.shortIndex a l) (s.shortIndex b l) (s.shortIndex_interior a l) (s.shortIndex_interior b l)
  simpa only [s.shortRail_slot] using hh

theorem source_target_connected (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (l : (PrimitiveCode.line s.code).Labels w) :
    SameComponent (inventory w hw v).board ((inventory w hw v).source (s.label l)) ((inventory w hw v).target (s.label l)) := by
  have hs : (inventory w hw v).source (s.label l) = s.actualEmbedding.cells (Line.cell w hw s.atoms s.code.initial l.val) :=
    (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells.injective (s.source_normal l |>.trans (s.placed_normal _).symm)
  have ht : (inventory w hw v).target (s.label l) = s.actualEmbedding.cells (Line.cell w hw s.atoms s.code.target l.val) :=
    (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells.injective (s.target_normal l |>.trans (s.placed_normal _).symm)
  rw [hs,ht]
  exact s.normal_connected hP hT _ _ l

end PushPuzzle.PushS.FiniteSourceInventory.LineSite
