/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceCapSideStock
public import PushS.FiniteSourceLineTerminalStock

/-! The genuine path propagation front reserves the complete strict line action footprint. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open scoped Classical

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

namespace PrimitiveProfile

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

theorem outside_subset_boxes (phase : Fin (codes w v).length → Bool)
    (selected : Finset (inventory w hw v).PhysicalLabel) :
    outside w hw v phase selected ⊆ boxes w hw v phase := by
  intro p hp
  obtain ⟨l,_,he⟩ := Finset.mem_image.mp hp
  exact Finset.mem_image.mpr ⟨l,Finset.mem_univ _,he⟩

end PrimitiveProfile

namespace LineSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

private theorem Selection.off_row_outside_avoids (H : s.Selection)
    (phase : Fin (codes w v).length → Bool) (p : Cell (Line.width w s.atoms) (Line.height w))
    (hp : p ∈ Line.Action.active w s.atoms s.code.above s.code.last) (hyne : p.2.val ≠ FiniteTools.radius w) :
    s.actualEmbedding.cells p ∉ PrimitiveProfile.outside w hw v phase (Finset.univ.map H.labels) := by
  apply fun h => (show s.actualEmbedding.cells p ∉ PrimitiveProfile.boxes w hw v phase from ?_)
    (PrimitiveProfile.outside_subset_boxes phase _ h)
  by_cases hlast : s.code.last = true
  · exact s.normal_cap_side_empty phase p hp hlast hyne
  · have hu := (Finset.mem_filter.mp hp).2
    have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    change FiniteTools.radius w-1 ≤ p.1.val ∧ p.1.val ≤ FiniteTools.radius w+Line.span w s.atoms+2 ∧
      FiniteTools.radius w-w-1 ≤ p.2.val ∧ p.2.val ≤ FiniteTools.radius w+w+1 ∧ _ at hb
    have hx : FiniteTools.radius w+1 ≤ p.1.val ∧ p.1.val ≤ FiniteTools.radius w+Line.span w s.atoms := by
      rcases hu with hu | hu | hu
      · exact (hyne hu.1).elim
      · exact hu
      · exact (hlast hu.1).elim
    exact s.normal_side_empty phase p hx.1 hx.2 hb.2.2.1 hb.2.2.2.1 hyne

private theorem Selection.action_outside_of_support (H : s.Selection) (ha : (inventory w hw v).Admissible)
    (hb : s.code.target = !s.code.initial) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool)
    (hcap : s.code.last = true → s.actualEmbedding.cells s.terminalSupport ∉ PrimitiveProfile.boxes w hw v phase)
    (p : Cell (Line.width w s.atoms) (Line.height w))
    (hp : p ∈ Line.Action.active w s.atoms s.code.above s.code.last) :
    s.actualEmbedding.cells p ∉ PrimitiveProfile.outside w hw v phase (Finset.univ.map H.labels) := by
  by_cases hy : p.2.val = FiniteTools.radius w
  · have hu := (Finset.mem_filter.mp hp).2
    have hbounds := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    change FiniteTools.radius w-1 ≤ p.1.val ∧ p.1.val ≤ FiniteTools.radius w+Line.span w s.atoms+2 ∧
      FiniteTools.radius w-w-1 ≤ p.2.val ∧ p.2.val ≤ FiniteTools.radius w+w+1 ∧ _ at hbounds
    have hx : FiniteTools.radius w ≤ p.1.val := by
      rcases hu with hu | hu | hu <;> omega
    by_cases hx' : p.1.val ≤ FiniteTools.radius w+Line.span w s.atoms+1
    · exact H.main_row_outside_avoids s ha hb hP hT phase p hx hx' hy
    · have hlast : s.code.last = true := by
        rcases hu with hu | hu | hu
        · omega
        · omega
        · exact hu.1
      have he : p = s.terminalSupport := s.eq_terminal_support p (by omega) hy
      rw [he]
      exact fun h => hcap hlast (PrimitiveProfile.outside_subset_boxes phase _ h)
  · exact H.off_row_outside_avoids s phase p hp hy

end LineSite

namespace PathSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec}
variable (s : PathSite w hw v P) (G : P.Geometry w)

theorem line_fixed_avoids (E : s.Endpoints) (ha : (inventory w hw v).Admissible)
    (hb : P.target = !P.initial) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (i : Fin P.segments.length)
    (F : PathEvent.Frontier s phase (.line i))
    (T : i.val+1 = P.segments.length → (s.line i).code.last = true → (s.line i).TerminalNeighbor phase) :
    ∀ p ∈ Line.Action.active w (s.line i).atoms (s.line i).code.above (s.line i).code.last,
      (s.line i).actualEmbedding.cells p ∉ PrimitiveProfile.outside w hw v phase
        (Finset.univ.map (s.selection G E i).labels) := by
  have hbline : (s.line i).code.target = !(s.line i).code.initial := by
    rw [s.line_target,s.line_initial]
    exact hb
  apply (s.selection G E i).action_outside_of_support (s.line i) ha hbline hP hT phase
  intro hlast
  by_cases hn : i.val+1 < P.segments.length
  · exact s.internal_terminal_empty G hb hP hT phase i F hn hlast
  · exact (T (by have hi := i.isLt; omega) hlast).support_empty (s.line i)

end PathSite
end PushPuzzle.PushS.FiniteSourceInventory
