/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceOutsideEndpoints
public import PushS.FiniteRoutingLineNeighbors

/-! The complete actual selected line reserves every working-row cell it executes. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.LineSite

open PushFS PushFS.Reduction FiniteRouting
open scoped Classical

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem Selection.normal_pair_outside_avoids (H : s.Selection) (ha : (inventory w hw v).Admissible)
    (hb : s.code.target = !s.code.initial) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (l : Line.Label w s.atoms) (n : ℕ)
    (hpos : ∀ q, Line.position w s.atoms q l = n+q.toNat)
    (p : Cell (Line.width w s.atoms) (Line.height w))
    (hx : FiniteTools.radius w+n ≤ p.1.val) (hx' : p.1.val ≤ FiniteTools.radius w+n+1)
    (hy : p.2.val = FiniteTools.radius w) :
    s.actualEmbedding.cells p ∉ PrimitiveProfile.outside w hw v phase (Finset.univ.map H.labels) := by
  have hlocal := Line.normal_adjacent_of_position w hw s.atoms l n hpos
  have hstep : ∃ d, Adjacent d ((inventory w hw v).source (H.labels l)) ((inventory w hw v).target (H.labels l)) := by
    rw [H.source,H.target,hb]
    cases he : s.code.initial
    · exact ⟨s.actualEmbedding.direction .east,s.actualEmbedding.adjacent _ _ _ hlocal⟩
    · exact ⟨s.actualEmbedding.direction .west,s.actualEmbedding.adjacent _ _ _ hlocal.reverse⟩
  obtain ⟨q,hq⟩ := Line.eq_normal_pair_cell w hw s.atoms l n hpos p hx hx' hy
  have hphase : q = s.code.initial ∨ q = s.code.target := by
    rw [hb]
    cases q <;> cases s.code.initial <;> decide
  obtain ⟨d,hd⟩ := hstep
  apply PrimitiveProfile.endpoint_pair_avoids ha hP hT phase _ (H.labels l)
    (Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩) d hd
  rcases hphase with hphase | hphase
  · left
    rw [H.source]
    exact congrArg s.actualEmbedding.cells (hq.trans (congrArg (fun q => Line.cell w hw s.atoms q l) hphase))
  · right
    rw [H.target]
    exact congrArg s.actualEmbedding.cells (hq.trans (congrArg (fun q => Line.cell w hw s.atoms q l) hphase))

theorem Selection.main_row_outside_avoids (H : s.Selection) (ha : (inventory w hw v).Admissible)
    (hb : s.code.target = !s.code.initial) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (p : Cell (Line.width w s.atoms) (Line.height w))
    (hx : FiniteTools.radius w ≤ p.1.val) (hx' : p.1.val ≤ FiniteTools.radius w+Line.span w s.atoms+1)
    (hy : p.2.val = FiniteTools.radius w) :
    s.actualEmbedding.cells p ∉ PrimitiveProfile.outside w hw v phase (Finset.univ.map H.labels) := by
  by_cases hfirst : p.1.val ≤ FiniteTools.radius w+1
  · apply H.normal_pair_outside_avoids s ha hb hP hT phase (Line.cutFirstLabel w s.atoms) 0 _ p (by omega) (by omega) hy
    intro q
    have he := Line.program_position_first w (segmentLength s.code.segment) (s.code.above != s.code.desiredSide) q
    change Line.position w s.atoms q (Line.firstLabel w s.atoms) = q.toNat at he
    have hl : Line.cutFirstLabel w s.atoms = Line.firstLabel w s.atoms := Fin.ext rfl
    rw [hl]
    simpa only [Nat.zero_add] using he
  by_cases hsecond : p.1.val ≤ FiniteTools.radius w+3
  · apply H.normal_pair_outside_avoids s ha hb hP hT phase (Line.secondLabel w _ _) 2 _ p (by omega) (by omega) hy
    exact Line.second_position w _ _
  by_cases hdeep : p.1.val+2 ≤ FiniteTools.radius w+Line.span w s.atoms
  · exact H.deep_row_outside_avoids s ha hP hT phase p (by omega) hdeep hy
  by_cases hlast : p.1.val < FiniteTools.radius w+Line.span w s.atoms
  · apply H.normal_pair_outside_avoids s ha hb hP hT phase (Line.penultimateLabel w _ _) (Line.span w s.atoms-2)
      (Line.penultimate_position w _ _) p _ _ hy
    all_goals have hl := s.good.2.1
    all_goals have hs : Line.span w s.atoms = segmentLength s.code.segment := Line.program_span_of_bound w _ _ hl
    all_goals omega
  · apply H.normal_pair_outside_avoids s ha hb hP hT phase (Line.cutLastLabel w s.atoms) (Line.span w s.atoms)
      (Line.position_last w s.atoms) p (by omega) hx' hy

end PushPuzzle.PushS.FiniteSourceInventory.LineSite
