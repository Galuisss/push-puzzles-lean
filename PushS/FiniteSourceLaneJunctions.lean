/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceNormalWalking
public import PushS.FiniteSourceDockGeometry
public import PushS.FiniteRoutingOuterLanes

/-! Adjacent collinear real line docks are joined by their actual clear outer lanes and one unit walk. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.LineSite

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Line.width Line.height

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s t : LineSite w hw v)

private theorem collinear_end_hub_adjacent (H : CollinearContract w s.code t.code)
    (hpos : ((codes w v).get s.index).1 = ((codes w v).get t.index).1) (north : Bool) :
    Adjacent (segmentDirection s.code.segment)
      (s.actualEmbedding.cells (s.endLane north))
      (t.actualEmbedding.cells (Line.outerCell w t.atoms north (Line.outerHubX w t.atoms))) := by
  apply adjacent_of_coordinates
  rw [s.actual_endLane_coordinates,t.actual_outerStart_coordinates]
  rw [←hpos,←H.directions,←H.joined,←Line.outerAlong_one]
  exact (shift_travels_iff (tileStride w*((codes w v).get s.index).1.1,tileStride w*((codes w v).get s.index).1.2)
    (segmentDirection s.code.segment) _ _).mpr (Line.outerAlong_step w _ s.code.segment.finish north)

theorem normal_collinear_docks (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool)
    (H : CollinearContract w s.code t.code)
    (hpos : ((codes w v).get s.index).1 = ((codes w v).get t.index).1) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (s.actualEmbedding.cells (Line.outerHub w s.atoms)))
      (PrimitiveProfile.state w hw v phase (t.actualEmbedding.cells (Line.outerHub w t.atoms))) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (t.actualEmbedding.cells (Line.outerHub w t.atoms)))
      (PrimitiveProfile.state w hw v phase (s.actualEmbedding.cells (Line.outerHub w s.atoms))) := by
  have hs : Line.span w s.atoms = segmentLength s.code.segment := Line.program_span_of_bound w _ _ s.good.2.1
  have ht : Line.span w t.atoms = segmentLength t.code.segment := Line.program_span_of_bound w _ _ t.good.2.1
  have hspos : 1 ≤ Line.span w s.atoms := by have h := s.good.2.1; omega
  have htpos : 1 ≤ Line.span w t.atoms := by have h := t.good.2.1; omega
  let xe : Fin (Line.width w s.atoms) := ⟨FiniteTools.radius w+Line.span w s.atoms,by unfold Line.width; omega⟩
  have Hstart := s.normal_outer_walk ha phase true (Line.outerHubX w s.atoms) xe
    (by dsimp [Line.outerHubX]; omega) (by dsimp [Line.outerHubX]; omega)
    (by dsimp [xe]; omega) (le_refl _)
  have Hend := s.normal_outer_walk ha phase true xe (Line.outerHubX w s.atoms)
    (by dsimp [xe]; omega) (le_refl _) (by dsimp [Line.outerHubX]; omega) (by dsimp [Line.outerHubX]; omega)
  have hf := s.normal_outer_free phase true xe (by dsimp [xe]; omega) (le_refl _)
  have hf' := t.normal_outer_free phase true (Line.outerHubX w t.atoms)
    (by dsimp [Line.outerHubX]; omega) (by dsimp [Line.outerHubX]; omega)
  have hadj := s.collinear_end_hub_adjacent t H hpos true
  have hstep := normal_profile_step w hw v ha phase _ _ _ hadj hf hf'
  have hback := normal_profile_step w hw v ha phase _ _ _ hadj.reverse hf' hf
  exact ⟨Hstart.trans hstep,hback.trans Hend⟩

end PushPuzzle.PushS.FiniteSourceInventory.LineSite
