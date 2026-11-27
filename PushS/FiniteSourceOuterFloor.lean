/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingOuterContacts
public import PushS.FiniteSourceLineConnectivity

/-! Both exposed lanes of every emitted line are floor on the complete thick-wall board. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem line_outer_wall_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point) (c : LineCode) (hc : (pos,PrimitiveCode.line c) ∈ codes w v)
    (hgood : LineGood w c.segment) (north : Bool) (n : ℕ) (hn0 : 1 ≤ n) (hn : n ≤ segmentLength c.segment)
    (t : GridRouting.Point × PrimitiveCode) (ht : t ∈ codes w v)
    (q : Cell (t.2.instanceOf w hw).width (t.2.instanceOf w hw).height) (hq : q ∈ (t.2.instanceOf w hw).board.walls) :
    macroShift w pos (c.laneWorld w hw hgood north n (by omega)) ≠ macroShift w t.1 (t.2.world w hw q) := by
  have hcl := code_local w v (pos,.line c) hc
  have htl := code_local w v t ht
  apply macro_outer_wall_ne w pos t.1 _ _
    (local_world_bounds w hw (.line c) (localCodes_fits w hw _ hcl) (c.laneSlot w hw hgood north n (by omega)))
    (local_world_bounds w hw t.2 (localCodes_fits w hw _ htl) q)
    (local_lane_collar_outer w hw _ c hcl hgood north n hn0 hn)
    (local_wall_collar_band_tight w hw _ _ htl q hq)
  intro hpos
  change c.laneWorld w hw hgood north n (by omega) ≠ t.2.world w hw q
  rw [c.laneWorld_actionWorld]
  apply local_action_ne_wall w hw (CellPlan.cell (v,pos)) c hcl _ _ t.2 _ q hq
  · apply c.outerCell_active w hw
    · dsimp only; omega
    · have hs := Line.program_span_of_bound w (segmentLength c.segment) (c.above != c.desiredSide) hgood.2.1
      dsimp only
      omega
  · simpa only [hpos] using htl

namespace LineSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

private theorem outerCell_coordinates (north : Bool) (x : Fin (Line.width w s.atoms))
    (hx : FiniteTools.radius w+1 ≤ x.val) (hx' : x.val ≤ FiniteTools.radius w+Line.span w s.atoms) :
    coordinates (s.actualEmbedding.cells (Line.outerCell w s.atoms north x)) =
      macroShift w ((codes w v).get s.index).1
        (s.code.laneWorld w hw s.good north (x.val-FiniteTools.radius w) (by
          have hs : Line.span w s.atoms = segmentLength s.code.segment :=
            Line.program_span_of_bound w _ _ s.good.2.1
          omega)) := by
  rw [s.actual_cell_coordinates]
  unfold LineCode.laneWorld LineCode.laneSlot
  congr 4
  apply Fin.ext
  change x.val = FiniteTools.radius w+(x.val-FiniteTools.radius w)
  omega

theorem outerCell_floor (north : Bool) (x : Fin (Line.width w s.atoms))
    (hx : FiniteTools.radius w+1 ≤ x.val) (hx' : x.val ≤ FiniteTools.radius w+Line.span w s.atoms) :
    s.actualEmbedding.cells (Line.outerCell w s.atoms north x) ∉ (inventory w hw v).walls := by
  intro hm
  obtain ⟨j,_,hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hm
  have hh := congrArg coordinates he
  rw [placed_wall_coordinates,s.outerCell_coordinates north x hx hx'] at hh
  have hs : Line.span w s.atoms = segmentLength s.code.segment :=
    Line.program_span_of_bound w _ _ s.good.2.1
  exact line_outer_wall_ne w hw v _ s.code s.code_mem s.good north (x.val-FiniteTools.radius w)
    (by omega) (by omega) _ (List.get_mem _ _) q hq hh.symm

end LineSite
end PushPuzzle.PushS.FiniteSourceInventory
