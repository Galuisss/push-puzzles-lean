/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteWalls
public import PushS.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-! Polynomial-time replacement of wall flags by ordinary boxes and goals. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteWalls

open PushFS
open Turing.MultiTapeTM ComputableInPolyTime
open scoped PushFS.Encoding

/-- A former wall is an ordinary box already on its goal. -/
def fillTile (t : Encoding.Tile) : Encoding.Tile :=
  ⟨false, t.goal || t.wall, t.box || t.wall, t.player⟩

/-- The dense output preserves the rectangle and maps each tile independently. -/
def fillData (d : Encoding.Data) : Encoding.Data :=
  ⟨d.width, d.height, d.rows.map (List.map fillTile)⟩

@[fun_prop] theorem fillData_polyTime :
    ComputableInPolyTime fillData Encoding.encData Encoding.encData := by
  have ht : ComputableInPolyTime fillTile Encoding.encTile Encoding.encTile := of_finite _
  unfold fillData
  fun_prop

private theorem fillTile_tile {w h : ℕ} (B : Board w h) (s : State w h) (p : Cell w h) :
    fillTile (Encoding.tile B s p) =
      Encoding.tile ⟨∅, B.goals ∪ B.walls⟩ ⟨s.player, s.boxes ∪ B.walls⟩ p := by
  simp [fillTile, Encoding.tile]

private theorem fillData_rows {w h : ℕ} (B : Board w h) (s : State w h) :
    (Encoding.rows B s).map (List.map fillTile) =
      Encoding.rows ⟨∅, B.goals ∪ B.walls⟩ ⟨s.player, s.boxes ∪ B.walls⟩ := by
  simp only [Encoding.rows, List.map_ofFn, Function.comp_def]
  congr 1
  funext y
  congr 1
  funext x
  exact fillTile_tile B s (x, y)

/-- The semantic compiler emits exactly the tilewise dense output. -/
theorem fillWalls_data (I : PushFS.Instance) :
    Encoding.data (fillWalls I).toInstance = fillData (Encoding.data I) := by
  change Encoding.Data.mk I.width I.height
      (Encoding.rows ⟨∅, I.board.goals ∪ I.board.walls⟩
        ⟨I.initial.player, I.initial.boxes ∪ I.board.walls⟩) = _
  unfold fillData Encoding.data
  exact congrArg (Encoding.Data.mk I.width I.height) (fillData_rows I.board I.initial).symm

/-- Filling every wall is a standard polynomial-time map of dense instances. -/
theorem fillWalls_polyTime :
    ComputableInPolyTime fillWalls PushFS.encoding PushS.encoding := by
  have hd : ComputableInPolyTime Encoding.data PushFS.encoding Encoding.encData :=
    of_eq fun _ => rfl
  exact (fillData_polyTime.comp hd).of_enc_eq
    (fun I => congrArg Encoding.encData (fillWalls_data I))

end PushPuzzle.PushS.FiniteWalls
