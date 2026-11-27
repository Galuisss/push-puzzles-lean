/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingSideCollars
public import PushS.FiniteSourceLineConnectivity
public import PushS.FiniteSourceLineGlyph
public import PushS.FiniteSourcePrimitiveProfile

/-! Actual full-board normal stocks leave every interior line-side lane empty. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

namespace PrimitiveProfile

/-- The current real owner phase selects the corresponding actual primitive actor. -/
private theorem position_coordinates (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : Fin (codes w v).length → Bool) (i : Fin (codes w v).length) (l : Label w v i) :
    coordinates (position w hw v phase ⟨i,l⟩) =
      macroShift w ((codes w v).get i).1 (((codes w v).get i).2.actor w hw (phase i) l) := by
  cases hphase : phase i
  · simp only [position,hphase,Bool.false_eq_true,ite_false]
    exact placed_source_coordinates w hw v i l
  · simp only [position,hphase,ite_true]
    exact placed_target_coordinates w hw v i l

/-- Pointwise exclusion of actual normal actors excludes their complete physical inventory. -/
theorem not_mem_of_actor_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : Fin (codes w v).length → Bool) (p : Cell (width w v) (height w v))
    (hne : ∀ (i : Fin (codes w v).length) (l : Label w v i), coordinates p ≠
      macroShift w ((codes w v).get i).1 (((codes w v).get i).2.actor w hw (phase i) l)) :
    p ∉ boxes w hw v phase := by
  intro hm
  obtain ⟨⟨i,l⟩,_,he⟩ := Finset.mem_image.mp hm
  have hcoord := congrArg coordinates he
  rw [position_coordinates w hw v phase i l] at hcoord
  exact hne i l hcoord.symm

/-- Local stock exclusion and an off-axis collar lift a real marker to the whole source board. -/
theorem marker_empty (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : Fin (codes w v).length → Bool) (pos : GridRouting.Point) (c : PrimitiveCode)
    (hc : (pos,c) ∈ codes w v)
    (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height)
    (hcollar : ∀ face, InCollar w face (c.world w hw p) →
      ¬SameLane face (Line.along w face (boundaryPoint w face) 0) (c.world w hw p))
    (hlocal : ∀ d ∈ localCodes w (CellPlan.cell (v,pos)), ∀ goal (l : d.Labels w),
      c.world w hw p ≠ d.actor w hw goal l)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos (c.world w hw p)) : q ∉ boxes w hw v phase := by
  have hcl := code_local w v (pos,c) hc
  apply not_mem_of_actor_ne w hw v phase q
  intro i l
  rw [hq]
  have ht := code_local w v _ (List.get_mem (codes w v) i)
  apply Ne.symm
  apply macro_actor_wall_ne w ((codes w v).get i).1 pos _ _
    (local_actor_bounds w hw _ (localCodes_fits w hw _ ht) (phase i) l)
    (local_world_bounds w hw c (localCodes_fits w hw _ hcl) p)
    (local_actor_collar_lane w hw _ _ ht (phase i) l) hcollar
  intro hpos
  apply Ne.symm
  exact hlocal _ (by simpa only [hpos] using ht) (phase i) l

end PrimitiveProfile

namespace LineSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

theorem normal_side_empty (phase : Fin (codes w v).length → Bool)
    (p : Cell (Line.width w s.atoms) (Line.height w))
    (hx : FiniteTools.radius w+1 ≤ p.1.val) (hx' : p.1.val ≤ FiniteTools.radius w+Line.span w s.atoms)
    (hy : FiniteTools.radius w-w-1 ≤ p.2.val) (hy' : p.2.val ≤ FiniteTools.radius w+w+1)
    (hyne : p.2.val ≠ FiniteTools.radius w) :
    s.actualEmbedding.cells p ∉ PrimitiveProfile.boxes w hw v phase := by
  have hc := code_local w v _ s.code_mem
  have hnear := s.code.interior_nearTrace w hw s.good p hx hx' hy hy'
  have hside := s.code.sideBand_of_interior w hw s.good p hx hx' hyne
  apply PrimitiveProfile.marker_empty w hw v phase _ (.line s.code) s.code_mem
    ((Line.rotation w _ (segmentDirection s.code.segment)).cells p)
    (local_side_collar_off_lane w hw _ s.code hc hnear hside)
    (fun d hd goal l => local_side_actor_ne w hw _ s.code hc p hnear hside d hd goal l)
    _ (s.actual_cell_coordinates p)

theorem outerCell_empty (phase : Fin (codes w v).length → Bool) (north : Bool)
    (x : Fin (Line.width w s.atoms)) (hx : FiniteTools.radius w+1 ≤ x.val)
    (hx' : x.val ≤ FiniteTools.radius w+Line.span w s.atoms) :
    s.actualEmbedding.cells (Line.outerCell w s.atoms north x) ∉ PrimitiveProfile.boxes w hw v phase := by
  apply s.normal_side_empty phase _ hx hx'
  all_goals cases north <;> dsimp [Line.outerCell,Line.laneY,FiniteTools.radius] <;> omega

end LineSite
end PushPuzzle.PushS.FiniteSourceInventory
