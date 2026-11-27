/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceLineConnectivity
public import PushS.FiniteSourceGateForward
public import PushS.FiniteGateOuterAccess

/-! The real core dock is exactly the real first B-arm line dock. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

namespace LineSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

theorem actual_outerStart_coordinates (north : Bool) :
    coordinates (s.actualEmbedding.cells (Line.outerCell w s.atoms north (Line.outerHubX w s.atoms))) =
      macroShift w ((codes w v).get s.index).1
        (Line.outerStart w (segmentDirection s.code.segment) s.code.segment.start north) := by
  have ht : Travels (segmentDirection s.code.segment) s.code.segment.start s.code.segment.finish (Line.span w s.atoms) := by
    change Travels _ _ _ (Line.span w (Line.program w (segmentLength s.code.segment) (s.code.above != s.code.desiredSide)))
    rw [Line.program_span_of_bound w _ _ s.good.2.1]
    exact segment_travels _ s.good.1
  have hh := Line.placement_outerStart w s.atoms (segmentDirection s.code.segment) s.code.segment.start s.code.segment.finish
    ht s.good.2.2.1 s.good.2.2.2 north
  change (PrimitiveCode.line s.code).world w hw
    ((Line.rotation w s.atoms (segmentDirection s.code.segment)).cells (Line.outerCell w s.atoms north (Line.outerHubX w s.atoms))) = _ at hh
  rw [s.actual_cell_coordinates,hh]

end LineSite

namespace CoreSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (c : CoreSite w hw v)

private theorem dock_eq_B_line_hub (s : LineSite w hw v)
    (hloc : ((codes w v).get s.index).1 = ((codes w v).get c.index).1)
    (hdir : segmentDirection s.code.segment = .north) (hstart : s.code.segment.start = corePort w c.gate.core.isAND 1) :
    c.dockCell = s.actualEmbedding.cells (Line.outerHub w s.atoms) := by
  have hleft := c.embedding_coordinates (FiniteGateFaceGeometry.dock w c.gate.core.isAND true)
  change coordinates c.dockCell = _ at hleft
  have hright := s.actual_outerStart_coordinates true
  rw [hloc,hdir,hstart] at hright
  rw [←FiniteGateOuterAccess.bDock_world] at hright
  have he : coordinates c.dockCell = coordinates (s.actualEmbedding.cells (Line.outerHub w s.atoms)) :=
    hleft.trans hright.symm
  exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

theorem dock_eq_B_arm_hub (p : PathSite w hw v (armSpec w c.gate 1))
    (i : Fin (armSpec w c.gate 1).segments.length) (hi : i.val = 0)
    (hloc : p.location = ((codes w v).get c.index).1) :
    c.dockCell = (p.line i).actualEmbedding.cells (Line.outerHub w (p.line i).atoms) := by
  apply c.dock_eq_B_line_hub (p.line i) ((p.line_location i).trans hloc)
  · change segmentDirection ((armSpec w c.gate 1).line i.val).segment = .north
    rw [hi,armSpec_first_direction]
    rfl
  · change ((armSpec w c.gate 1).line i.val).segment.start = _
    rw [hi,armSpec_first_start]

end CoreSite
end PushPuzzle.PushS.FiniteSourceInventory
