/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteBlocks
public import PushS.FiniteSourceInventory
public import PushS.FiniteWallEncoding
import Mathlib.Tactic.FinCases

/-! Every wall in the complete actual source output belongs to a frozen full block. -/

@[expose] public section
namespace PushPuzzle.PushS

open PushFS PushFS.Reduction FiniteFreeze FiniteGeometry

namespace FiniteGeometry

private theorem andWalls_boundedSquares (w : ℕ) (hw : 0 < w) : BoundedSquares w (andWalls w) := by
  apply BoundedSquares.biUnion
  intro i _
  have ht := andRectangle_thick w i
  have hb := andRectangle_interior w i
  exact (andRectangle w i).boundedSquares _ _ w hw ht.1 ht.2 (by omega) (by omega)

private theorem orWalls_boundedSquares (w : ℕ) (hw : 0 < w) : BoundedSquares w (orWalls w) := by
  apply BoundedSquares.biUnion
  intro i _
  have ht := orRectangle_thick w i
  have hb := orRectangle_interior w i
  exact (orRectangle w i).boundedSquares _ _ w hw ht.1 ht.2 (by omega) (by omega)

end FiniteGeometry

namespace FiniteRouting.Line

attribute [local irreducible] width height

private theorem walls_boundedSquares (w : ℕ) (hw : 0 < w) (atoms : List Atom) (above : Bool)
    (ha : ∀ a ∈ atoms, a.Valid w) : BoundedSquares w (walls w atoms above) := by
  apply BoundedSquares.biUnion
  intro r hr
  have ht := rectangles_thick w 0 above atoms ha (List.mem_toFinset.mp hr)
  have hb := rectangles_bounds w 0 above atoms (List.mem_toFinset.mp hr)
  apply r.boundedSquares _ _ w hw ht.1 ht.2
  · unfold width
    omega
  · unfold height
    exact hb.2.2.2

private theorem rotation_boundedSquares (w : ℕ) (atoms : List Atom) (d : Direction)
    {walls : Finset (Cell (width w atoms) (height w))} (hs : BoundedSquares w walls) :
    BoundedSquares w (walls.map (rotation w atoms d).cells.toEmbedding) := by
  cases d with
  | north => exact hs.counterclockwise
  | east =>
    change BoundedSquares w (walls.map (Function.Embedding.refl _))
    simpa only [Finset.map_refl] using hs
  | south => exact hs.clockwise
  | west =>
    simpa only [rotation,orientedWidth,orientedHeight,GridIsometry.trans,Equiv.trans_toEmbedding,Finset.map_map]
      using hs.reflectX.reflectY

end FiniteRouting.Line

namespace FiniteRouting.Turn

private theorem walls_boundedSquares (w : ℕ) (hw : 0 < w) : BoundedSquares w
    (FiniteTools.turnWalls w) := by
  apply BoundedSquares.biUnion
  intro i _
  have ht := FiniteTools.turnRectangle_thick w i
  apply (FiniteTools.turnRectangle w i).boundedSquares _ _ w hw ht.1 ht.2
  all_goals fin_cases i <;> simp [FiniteTools.turnRectangle,FiniteTools.side,FiniteTools.radius] <;> omega

private theorem quarter_boundedSquares (w : ℕ) (d : Direction)
    {walls : Finset (Cell (FiniteTools.side w) (FiniteTools.side w))} (hs : BoundedSquares w walls) :
    BoundedSquares w (walls.map (quarter w d).cells.toEmbedding) := by
  cases d with
  | north => exact hs.counterclockwise
  | east => simpa only [quarter,GridIsometry.refl,Equiv.refl_toEmbedding,Finset.map_refl] using hs
  | south => exact hs.clockwise
  | west =>
    simpa only [quarter,GridIsometry.trans,Equiv.trans_toEmbedding,Finset.map_map]
      using hs.reflectX.reflectY

private theorem orientation_boundedSquares (w : ℕ) (d e : Direction)
    {walls : Finset (Cell (FiniteTools.side w) (FiniteTools.side w))} (hs : BoundedSquares w walls) :
    BoundedSquares w (walls.map (orientation w d e).cells.toEmbedding) := by
  unfold orientation
  split_ifs
  · simpa only [GridIsometry.trans,Equiv.trans_toEmbedding,← Finset.map_map,
      GridIsometry.refl,Equiv.refl_toEmbedding,Finset.map_refl] using quarter_boundedSquares w d hs
  · simpa only [GridIsometry.trans,Equiv.trans_toEmbedding,← Finset.map_map]
      using quarter_boundedSquares w d hs.reflectY

end FiniteRouting.Turn

namespace FiniteRouting.PrimitiveCode

/-- All walls of each exact emitted primitive have complete width-`w` square covers. -/
private theorem walls_boundedSquares (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) :
    BoundedSquares w (c.instanceOf w hw).board.walls := by
  cases c with
  | core g =>
    rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
    cases kind
    · exact orWalls_boundedSquares w (by omega)
    · exact andWalls_boundedSquares w (by omega)
  | line c =>
    exact Line.rotation_boundedSquares w _ _
      (Line.walls_boundedSquares w (by omega) _ c.above (Line.program_valid _ _ _))
  | turn c =>
    exact Turn.orientation_boundedSquares w _ _ (Turn.walls_boundedSquares w (by omega))

end FiniteRouting.PrimitiveCode

namespace FiniteSourceInventory

open Turing.MultiTapeTM

/-- Literal primitive wall union, without any geometric disjointness requirement. -/
private theorem walls_boundedSquares (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) :
    BoundedSquares w (inventory w hw v).walls := by
  apply BoundedSquares.biUnion
  intro i _
  exact (((codes w v).get i).2.walls_boundedSquares w hw).translate
    _ _ ((inventory w hw v).fitsX i) ((inventory w hw v).fitsY i)

/-- The entire actual wall union is frozen at every smaller force. -/
theorem walls_thick (k : ℕ) (hk : 1 ≤ k) (v : CellPlan.Source) :
    Thick k (inventory (k+1) (by omega) v).walls :=
  (walls_boundedSquares (k+1) (by omega) v).thick (by omega)

theorem fillWalls_solvable_iff (k : ℕ) (hk : 1 ≤ k) (v : CellPlan.Source)
    (ha : (inventory (k+1) (by omega) v).Admissible) :
    (FiniteWalls.fillWalls (puzzle (k+1) (by omega) v ha)).SolvableFinite k ↔
      (puzzle (k+1) (by omega) v ha).Solvable (some k) :=
  FiniteWalls.fillWalls_solvable_iff _ (walls_thick k hk v)

/-- The actual complete no-wall bitmap emitted by the source compiler. -/
def wallFreeData (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) : Encoding.Data :=
  FiniteWalls.fillData ((table w hw).data v)

theorem wallFreeData_polyTime (w : ℕ) (hw : 2 ≤ w) :
    ComputableInPolyTime (wallFreeData w hw) CellPlan.encSource Encoding.encData :=
  FiniteWalls.fillData_polyTime.comp (data_polyTime w hw)

end FiniteSourceInventory
end PushPuzzle.PushS
