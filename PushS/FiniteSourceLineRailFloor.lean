/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceLineConnectivity
public import PushS.FiniteSourceLineBeforeCaps

/-! Full literal static readout rails, including both support caps, survive the actual source wall union. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory.LineSite

open PushFS PushFS.Reduction FiniteRouting

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem rail_floor (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (i : Fin (Line.span w s.atoms+4)) :
    s.actualEmbedding.cells (Line.Readout.rail w s.atoms i) ∉ (inventory w hw v).walls := by
  have hspan : Line.span w s.atoms = segmentLength s.code.segment := Line.program_span_of_bound w _ _ s.good.2.1
  by_cases hz : i.val = 0
  · apply line_before_cap_floor w hw v hP hT _ s.code s.code_mem
    rw [s.actual_cell_coordinates]
    unfold LineCode.capWorld LineCode.capSlot
    simp only [LineCode.capIndex,↓reduceIte]
    congr 4
    exact Fin.ext hz
  by_cases hl : i.val = Line.span w s.atoms+3
  · apply line_after_cap_floor w hw v hP hT _ s.code s.code_mem
    rw [s.actual_cell_coordinates]
    unfold LineCode.capWorld LineCode.capSlot
    simp only [LineCode.capIndex,Bool.false_eq_true,↓reduceIte]
    congr 4
    exact Fin.ext hl
  · have hi : i.val-1 ≤ segmentLength s.code.segment+1 := by have h := i.isLt; omega
    apply row_floor w hw v _ s.code s.code_mem s.good (i.val-1) hi
    rw [s.actual_cell_coordinates]
    have hr : Line.Readout.rail w s.atoms i =
        (Line.railEmbedding w s.atoms).cells (⟨i.val-1,by omega⟩,Line.railRow w) := by
      apply Prod.ext <;> apply Fin.ext
      · dsimp [Line.Readout.rail,Line.railEmbedding,GridEmbedding.translate]
        unfold FiniteTools.radius
        omega
      · dsimp [Line.Readout.rail,Line.railEmbedding,GridEmbedding.translate,Line.railRow,Line.workY]
        omega
    rw [hr]
    rfl

theorem rail_normal_floor_actual (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (i : Fin (Line.span w s.atoms+4)) :
    s.canonicalEmbedding.cells (Line.Readout.rail w s.atoms i) ∉
      ((s.orientation.inverse.axis (width w v) (height w v)).geometry.board (inventory w hw v).board).walls := by
  rw [←s.placed_normal]
  intro hm
  exact s.rail_floor hP hT i ((GridIsometry.mem_walls _ _ _).mp hm)

end PushPuzzle.PushS.FiniteSourceInventory.LineSite
