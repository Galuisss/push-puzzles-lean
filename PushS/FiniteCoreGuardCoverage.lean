/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingInitialFaces
public import PushS.FiniteRoutingActionGuards
public import PushS.FiniteRoutingWorldCoordinates

public import PushS.FiniteGeometrySimp

/-! The outward portions of every real core wall are exactly the initial line's finite stock collar. -/

public section
namespace PushPuzzle.PushS.FiniteCoreGuardCoverage

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry

attribute [local irreducible] FiniteGeometry.side Line.width Line.height Line.program Line.span

attribute [local finite_core_coords]
  Outward Line.PerpendicularBand Line.GuardSide coreSide PortAnnulus.innerDirection corePort coreWorld orRectangle Nearby Line.along coreOffset padding spacing origin andRectangle

/-- The literal wall set of the selected gate kind. -/
@[expose] def walls (w : ℕ) (kind : Bool) : Finset (Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) := if kind then andWalls w else orWalls w

/-- The scalar-zero world anchor of a canonical outward core port. -/
@[expose] def portAnchor (w : ℕ) (kind : Bool) (role : Fin 3) : ℕ × ℕ :=
  Line.along w (PortAnnulus.innerDirection role) (corePort w kind role) 0

attribute [local finite_core_coords] portAnchor

/-- Every outward core wall lies on the literal initial stock guard side, within its width and first `2w+12` columns. -/
private theorem wall_outward_band (w : ℕ) (hw : 2 ≤ w) (kind : Bool) (role : Fin 3)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ walls w kind)
    (ho : Outward (PortAnnulus.innerDirection role) (portAnchor w kind role) (coreWorld w p)) :
    Line.PerpendicularBand w (PortAnnulus.innerDirection role) (portAnchor w kind role) (coreWorld w p) ∧
      Line.GuardSide (PortAnnulus.innerDirection role) (coreSide kind role) (portAnchor w kind role) (coreWorld w p) ∧
      Nearby (2*w+11) (portAnchor w kind role) (coreWorld w p) := by
  cases kind with
  | false =>
    change p ∈ orWalls w at hp
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    have hb := (Rectangle.mem_cells (orRectangle w i) _ _ p).mp hi
    fin_cases role <;> fin_cases i <;>
      simp [finite_core_coords] at hb ho ⊢ <;> omega
  | true =>
    change p ∈ andWalls w at hp
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    have hb := (Rectangle.mem_cells (andRectangle w i) _ _ p).mp hi
    fin_cases role <;> fin_cases i <;>
      simp [finite_core_coords] at hb ho ⊢ <;> omega

/-- A literal line cell at or after its first column is physically outward of the placed port. -/
private theorem placement_outward (w : ℕ) (atoms : List Line.Atom) (d : Direction) (start finish : ℕ × ℕ)
    (ht : Travels d start finish (Line.span w atoms))
    (hs : start.1 ≤ tileStride w ∧ start.2 ≤ tileStride w)
    (hf : finish.1 ≤ tileStride w ∧ finish.2 ≤ tileStride w)
    (a : Cell (Line.width w atoms) (Line.height w)) (ha : FiniteTools.radius w ≤ a.1.val) :
    Outward d (Line.along w d start 0)
      (coordinates ((Line.placement w atoms d start finish ht hs hf).cells a)) := by
  have hax := a.1.isLt
  have hay := a.2.isLt
  rw [Line.placement_coordinates]
  cases d <;> dsimp [Line.rotatedCoordinates,Outward,Line.along,Travels,Line.offsetX,Line.offsetY,Line.anchor] at * <;>
    unfold Line.width Line.height FiniteTools.side FiniteTools.radius padding at * <;> omega

/-- The physical point is at most `n` outward columns beyond its port anchor. -/
@[expose] def BeforeColumn (d : Direction) (start point : ℕ × ℕ) (n : ℕ) : Prop :=
  match d with
  | .east => point.1 ≤ start.1+n
  | .south => point.2 ≤ start.2+n
  | .west => start.1 ≤ point.1+n
  | .north => start.2 ≤ point.2+n

/-- A literal world longitudinal bound gives the same bound on the line's actual unrotated column. -/
theorem column_le_of_world_limit (w : ℕ) (atoms : List Line.Atom) (d : Direction) (start finish : ℕ × ℕ)
    (ht : Travels d start finish (Line.span w atoms))
    (hs : start.1 ≤ tileStride w ∧ start.2 ≤ tileStride w)
    (hf : finish.1 ≤ tileStride w ∧ finish.2 ≤ tileStride w)
    (a : Cell (Line.width w atoms) (Line.height w)) (n : ℕ)
    (hn : BeforeColumn d (Line.along w d start 0)
      (coordinates ((Line.placement w atoms d start finish ht hs hf).cells a)) n) :
    a.1.val ≤ FiniteTools.radius w+n := by
  have hax := a.1.isLt
  have hay := a.2.isLt
  rw [Line.placement_coordinates] at hn
  cases d <;> dsimp [BeforeColumn,Line.rotatedCoordinates,Line.along,Travels,Line.offsetX,Line.offsetY,Line.anchor] at * <;>
    unfold Line.width Line.height FiniteTools.side FiniteTools.radius padding at * <;> omega

/-- An initial stock band keeps its literal above/below guard side under the actual proper rotation. -/
theorem placed_stock_band_guard (w : ℕ) (atoms : List Line.Atom) (above : Bool)
    (d : Direction) (start finish : ℕ × ℕ)
    (ht : Travels d start finish (Line.span w atoms))
    (hs : start.1 ≤ tileStride w ∧ start.2 ≤ tileStride w)
    (hf : finish.1 ≤ tileStride w ∧ finish.2 ≤ tileStride w)
    (a : Cell (Line.width w atoms) (Line.height w)) (hb : Line.StockBand w above a.2.val) :
    Line.GuardSide d above (Line.along w d start 0)
      (coordinates ((Line.placement w atoms d start finish ht hs hf).cells a)) := by
  have hax := a.1.isLt
  have hay := a.2.isLt
  rw [Line.placement_coordinates]
  cases d <;> cases above <;> dsimp [Line.StockBand,Line.GuardSide,Line.rotatedCoordinates,Line.along,Travels,
    Line.offsetX,Line.offsetY,Line.anchor] at * <;>
    unfold Line.width Line.height FiniteTools.side FiniteTools.radius padding at * <;> omega

/-- Literal guard-side, width and longitudinal bounds identify a cell of the initial stock wall. -/
private theorem initial_stock_of_world_band (w length : ℕ) (switch above : Bool)
    (d : Direction) (start finish : ℕ × ℕ)
    (ht : Travels d start finish (Line.span w (Line.program w length switch)))
    (hs : start.1 ≤ tileStride w ∧ start.2 ≤ tileStride w)
    (hf : finish.1 ≤ tileStride w ∧ finish.2 ≤ tileStride w)
    (a : Cell (Line.width w (Line.program w length switch)) (Line.height w))
    (ha : FiniteTools.radius w ≤ a.1.val)
    (hb : Line.PerpendicularBand w d (Line.along w d start 0)
      (coordinates ((Line.placement w (Line.program w length switch) d start finish ht hs hf).cells a)))
    (hg : Line.GuardSide d above (Line.along w d start 0)
      (coordinates ((Line.placement w (Line.program w length switch) d start finish ht hs hf).cells a)))
    (hn : Nearby (2*w+11) (Line.along w d start 0)
      (coordinates ((Line.placement w (Line.program w length switch) d start finish ht hs hf).cells a))) :
    a ∈ Line.walls w (Line.program w length switch) above := by
  have hax := a.1.isLt
  have hay := a.2.isLt
  have hh : a.1.val < FiniteTools.radius w+2*Line.buffer w+2 ∧ Line.StockBand w above a.2.val := by
    rw [Line.placement_coordinates] at hb hg hn
    cases d <;> cases above <;>
      dsimp [Line.PerpendicularBand,Line.GuardSide,Line.StockBand,Nearby,Line.rotatedCoordinates,Line.along,
        Travels,Line.offsetX,Line.offsetY,Line.anchor] at * <;>
      unfold Line.width Line.height Line.buffer FiniteTools.side FiniteTools.radius padding at * <;> constructor <;> omega
  exact Line.program_first_stock_wall w length switch above a ha hh.1 hh.2

/-- The literal first-arm placement and its finite source-tile bounds. -/
structure InitialArmPlacement (w length : ℕ) (kind switch : Bool) (role : Fin 3) where
  finish : ℕ × ℕ
  travels : Travels (PortAnnulus.innerDirection role) (corePort w kind role) finish
    (Line.span w (Line.program w length switch))
  start_fits : (corePort w kind role).1 ≤ tileStride w ∧ (corePort w kind role).2 ≤ tileStride w
  finish_fits : finish.1 ≤ tileStride w ∧ finish.2 ≤ tileStride w

private theorem placement_stock_cover (w length : ℕ) (hw : 2 ≤ w) (kind switch : Bool) (role : Fin 3)
    (C : InitialArmPlacement w length kind switch role)
    (a : Cell (Line.width w (Line.program w length switch)) (Line.height w))
    (ha : FiniteTools.radius w ≤ a.1.val)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ walls w kind)
    (he : coordinates ((Line.placement w (Line.program w length switch) (PortAnnulus.innerDirection role)
      (corePort w kind role) C.finish C.travels C.start_fits C.finish_fits).cells a) = coreWorld w p) :
    a ∈ Line.walls w (Line.program w length switch) (coreSide kind role) := by
  rcases C with ⟨finish,ht,hs,hf⟩
  have ho := placement_outward w (Line.program w length switch) (PortAnnulus.innerDirection role)
    (corePort w kind role) finish ht hs hf a ha
  rw [he] at ho
  obtain ⟨hb,hg,hn⟩ := wall_outward_band w hw kind role p hp ho
  apply initial_stock_of_world_band w length switch (coreSide kind role) (PortAnnulus.innerDirection role)
    (corePort w kind role) finish ht hs hf a ha
  · exact he.symm ▸ hb
  · exact he.symm ▸ hg
  · exact he.symm ▸ hn

/-- Every real core wall encountered at an actual initial line's active column is already one of that line's own stock walls. -/
theorem initial_stock_covers_core_wall (w length : ℕ) (hw : 2 ≤ w) (kind switch : Bool) (role : Fin 3)
    (finish : ℕ × ℕ)
    (ht : Travels (PortAnnulus.innerDirection role) (corePort w kind role) finish
      (Line.span w (Line.program w length switch)))
    (hs : (corePort w kind role).1 ≤ tileStride w ∧ (corePort w kind role).2 ≤ tileStride w)
    (hf : finish.1 ≤ tileStride w ∧ finish.2 ≤ tileStride w)
    (a : Cell (Line.width w (Line.program w length switch)) (Line.height w))
    (ha : FiniteTools.radius w ≤ a.1.val)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ walls w kind)
    (he : coordinates ((Line.placement w (Line.program w length switch) (PortAnnulus.innerDirection role)
      (corePort w kind role) finish ht hs hf).cells a) = coreWorld w p) :
    a ∈ Line.walls w (Line.program w length switch) (coreSide kind role) :=
  placement_stock_cover w length hw kind switch role ⟨finish,ht,hs,hf⟩ a ha p hp he

end PushPuzzle.PushS.FiniteCoreGuardCoverage
