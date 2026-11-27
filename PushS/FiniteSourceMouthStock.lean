/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceDeepStock
public import PushS.FiniteRoutingMouthStock

/-! Both mandatory flip mouths are empty in every actual normal primitive profile. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.LineSite

open PushFS PushFS.Reduction FiniteRouting

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

theorem normal_first_mouth_empty (phase : Fin (codes w v).length → Bool) (j : Fin 2)
    (p : Cell (Line.width w s.atoms) (Line.height w))
    (hx : p.1.val = FiniteTools.radius w+2*Line.buffer w+w+1+j.val)
    (hy : FiniteTools.radius w-w-1 ≤ p.2.val) (hy' : p.2.val ≤ FiniteTools.radius w+w+1) :
    s.actualEmbedding.cells p ∉ PrimitiveProfile.boxes w hw v phase := by
  let n := 2*Line.buffer w+w+1+j.val
  have hj := j.isLt
  have hl := s.good.2.1
  have hspan : Line.span w s.atoms = segmentLength s.code.segment := Line.program_span_of_bound w _ _ hl
  have hn : 3 ≤ n := by dsimp [n,Line.buffer]; omega
  have hn' : n+2 ≤ segmentLength s.code.segment := by dsimp [n,Line.buffer]; omega
  have hx0 : FiniteTools.radius w+1 ≤ p.1.val := by dsimp [n] at hn; omega
  have hx1 : p.1.val ≤ FiniteTools.radius w+Line.span w s.atoms := by dsimp [n] at hn'; omega
  by_cases hrow : p.2.val = FiniteTools.radius w
  · apply deep_stock_empty w hw v phase ((codes w v).get s.index).1 s.code s.code_mem n hn hn'
      (s.code.first_mouth_actor_ne w hw s.good j)
    have hworld := s.code.actionWorld_on_row w hw s.good p (Nat.le_trans (Nat.le_succ _) hx0) (Nat.le_trans hx1 (Nat.le_succ _)) hrow
    have hnpos : p.1.val-FiniteTools.radius w = n := by dsimp [n]; omega
    rw [hnpos] at hworld
    exact (s.actual_cell_coordinates p).trans (congrArg (macroShift w ((codes w v).get s.index).1) hworld)
  · exact s.normal_side_empty phase p hx0 hx1 hy hy' hrow

end PushPuzzle.PushS.FiniteSourceInventory.LineSite
