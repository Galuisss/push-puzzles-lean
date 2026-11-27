/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingMouthStock
public import PushS.FiniteSourceDeepStock
public import PushS.FiniteSourceLineForward
public import PushS.FiniteSourceCodeOrder
public import PushS.FiniteSourceTravelHulls

/-! Actual normal travel hulls exclude fixed outside stock on a selected line's interior row. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open scoped Classical

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

namespace PrimitiveProfile

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

theorem position_hull (phase : Fin (codes w v).length → Bool) (l : (inventory w hw v).PhysicalLabel) :
    Hull (coordinates ((inventory w hw v).source l)) (coordinates ((inventory w hw v).target l))
      (coordinates (position w hw v phase l)) := by
  unfold position
  split <;> dsimp [Hull] <;> omega

/-- A complete owner selection reserves all of its physical normal travel hulls. -/
private theorem owned_hull_avoids (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (selected : Finset (inventory w hw v).PhysicalLabel)
    (i : Fin (codes w v).length) (hcover : (inventory w hw v).pieceLabels i ⊆ selected)
    (l : (inventory w hw v).PhysicalLabel) (hl : l.1 = i)
    (p : Cell (width w v) (height w v))
    (hp : Hull (coordinates ((inventory w hw v).source l)) (coordinates ((inventory w hw v).target l)) (coordinates p)) :
    p ∉ outside w hw v phase selected := by
  intro hm
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hm
  have hjnot := (Finset.mem_sdiff.mp hj).2
  by_cases howner : j.1 = i
  · exact hjnot (hcover ((inventory w hw v).mem_pieceLabels i j |>.mpr howner))
  · have hne : l.1 ≠ j.1 := by rw [hl]; exact Ne.symm howner
    have hstock := position_hull phase j
    rw [he] at hstock
    exact normal_travel_hulls_disjoint w hw v hP hT l j hne (coordinates p) hp hstock

end PrimitiveProfile

namespace LineSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

theorem Selection.deep_row_outside_avoids (H : s.Selection) (ha : (inventory w hw v).Admissible)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (p : Cell (Line.width w s.atoms) (Line.height w))
    (hx : FiniteTools.radius w+3 ≤ p.1.val) (hx' : p.1.val+2 ≤ FiniteTools.radius w+Line.span w s.atoms)
    (hy : p.2.val = FiniteTools.radius w) :
    s.actualEmbedding.cells p ∉ PrimitiveProfile.outside w hw v phase (Finset.univ.map H.labels) := by
  let n := p.1.val-FiniteTools.radius w
  have hspan : Line.span w s.atoms = segmentLength s.code.segment := Line.program_span_of_bound w _ _ s.good.2.1
  have hn : 3 ≤ n := by dsimp [n]; omega
  have hn' : n+2 ≤ segmentLength s.code.segment := by dsimp [n]; omega
  have hwrow := s.code.actionWorld_on_row w hw s.good p (by omega)
    (show p.1.val ≤ FiniteTools.radius w+Line.span w s.atoms+1 by omega) hy
  have hq : coordinates (s.actualEmbedding.cells p) = macroShift w ((codes w v).get s.index).1
      (Line.along w (segmentDirection s.code.segment) s.code.segment.start n) :=
    (s.actual_cell_coordinates p).trans (congrArg (macroShift w ((codes w v).get s.index).1) hwrow)
  by_cases hnormal : ∃ goal l, Line.along w (segmentDirection s.code.segment) s.code.segment.start n =
      (PrimitiveCode.line s.code).actor w hw goal l
  · obtain ⟨goal,l,he⟩ := hnormal
    apply PrimitiveProfile.owned_hull_avoids hP hT phase _ s.index (H.cover s ha) (s.label l)
      (primitiveLabel_owner w hw v s.index (.line s.code) s.code_eq l)
    have heq : coordinates (s.actualEmbedding.cells p) = coordinates
        (if goal then (inventory w hw v).target (s.label l) else (inventory w hw v).source (s.label l)) := by
      rw [hq,he]
      cases goal
      · exact (source_primitiveLabel_coordinates w hw v s.index (.line s.code) s.code_eq l).symm
      · exact (target_primitiveLabel_coordinates w hw v s.index (.line s.code) s.code_eq l).symm
    rw [heq]
    cases goal <;> dsimp [Hull] <;> omega
  · have hempty := deep_stock_empty w hw v phase ((codes w v).get s.index).1 s.code s.code_mem n hn hn'
      (by intro goal l he; exact hnormal ⟨goal,l,he⟩) _ hq
    intro hm
    apply hempty
    obtain ⟨l,_,he⟩ := Finset.mem_image.mp hm
    exact Finset.mem_image.mpr ⟨l,Finset.mem_univ _,he⟩

end LineSite
end PushPuzzle.PushS.FiniteSourceInventory
