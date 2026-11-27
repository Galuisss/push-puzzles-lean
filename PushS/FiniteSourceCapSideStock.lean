/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingCapSideCollars
public import PushS.FiniteSourceSideStock

/-! The off-row terminal cap of every actual straight-ending primitive has empty normal stock. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

namespace LineSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

theorem normal_cap_side_empty (phase : Fin (codes w v).length → Bool)
    (p : Cell (Line.width w s.atoms) (Line.height w))
    (hp : p ∈ Line.Action.active w s.atoms s.code.above s.code.last)
    (hlast : s.code.last = true) (hy : p.2.val ≠ FiniteTools.radius w) :
    s.actualEmbedding.cells p ∉ PrimitiveProfile.boxes w hw v phase := by
  have hc := code_local w v _ s.code_mem
  have hnear : s.code.NearTrace w (s.code.actionWorld w hw p) := s.code.action_footprint w hw s.good p hp
  have hx : FiniteTools.radius w+1 ≤ p.1.val := by
    have hu := (Finset.mem_filter.mp hp).2
    rcases hu with hu | hu | hu
    · exact (hy hu.1).elim
    · exact hu.1
    · omega
  have hside := s.code.cap_side_band_of_cell w hw s.good p hx hy
  exact PrimitiveProfile.marker_empty w hw v phase _ (.line s.code) s.code_mem
    ((Line.rotation w _ (segmentDirection s.code.segment)).cells p)
    (local_cap_side_collar_off_lane w hw _ s.code hc hnear hside)
    (fun d hd goal l => local_cap_side_actor_ne w hw _ s.code hc p hnear hside hlast d hd goal l)
    _ (s.actual_cell_coordinates p)

end LineSite
end PushPuzzle.PushS.FiniteSourceInventory
