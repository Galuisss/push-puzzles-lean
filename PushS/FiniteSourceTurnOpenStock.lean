/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingTurnOpenStock
public import PushS.FiniteSourceTurnConnectivity
public import PushS.FiniteSourceSideStock

/-! The literal center and open quadrant of each emitted turn avoid the complete normal inventory. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

namespace TurnSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : TurnSite w hw v)

theorem open_gap_empty (phase : Fin (codes w v).length → Bool)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hp : p ∈ FiniteTools.turnActive w) (hgap : Turn.OpenGap w p) :
    s.actualEmbedding.cells p ∉ PrimitiveProfile.boxes w hw v phase := by
  have hc := code_local w v _ s.code_mem
  have hinterior := local_turn_window_interior w hw _ s.code hc
    ((Turn.orientation w s.code.incoming s.code.outgoing).cells p)
  exact PrimitiveProfile.marker_empty w hw v phase _ (.turn s.code) s.code_mem
    ((Turn.orientation w s.code.incoming s.code.outgoing).cells p)
    (fun face hf => ((interior_not_collar w face hinterior) hf).elim)
    (fun d hd goal l => local_open_gap_actor_ne w hw _ s.code hc p hp hgap d hd goal l)
    _ (s.actual_cell_coordinates p)

end TurnSite
end PushPuzzle.PushS.FiniteSourceInventory
