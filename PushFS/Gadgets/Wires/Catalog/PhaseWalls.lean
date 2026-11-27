/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.CellCatalog

/-! The actual complete ordinary physical-cell wall sets are independent of the endpoint phases. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog


open Reduction
set_option maxRecDepth 65536

private theorem placed_wallset {I : Instance} {L : Type} [Fintype L] {W H : ℕ}
    (M : SlotMatching I L) (dx dy : ℕ) (hx : dx+I.width≤W) (hy : dy+I.height≤H) :
    (placedAtlas M dx dy hx hy).board.walls=I.board.walls.map (GridEmbedding.translate dx dy hx hy).cells := by
  change (Finset.univ.biUnion fun _ : Fin 1=>I.board.walls.map (GridEmbedding.translate dx dy hx hy).cells)=_
  ext p
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
  exact ⟨fun ⟨_,hp⟩=>hp,fun hp=>⟨0,hp⟩⟩

private theorem walls_eq (k : Kind) (a b c d : Bool) : (atlas k a b).walls=(atlas k c d).walls := by
  change (placedAtlas (baseMatching k a b) (dx k) (dy k) (fitsX k a b) (fitsY k a b)).board.walls=
    (placedAtlas (baseMatching k c d) (dx k) (dy k) (fitsX k c d) (fitsY k c d)).board.walls
  cases k
  all_goals rw [placed_wallset,placed_wallset]
  all_goals dsimp only [base,Instance.reflectedX,Instance.transposed,GridIsometry.reorientInstance,
    GridIsometry.board,StorageAtlas.puzzle,StorageAtlas.board,Chain.puzzle,Chain.board,dx,dy]
  · change (Polyline.L.atlas 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).walls.map _=
      (Polyline.L.atlas 99970 98999 (by decide) (by decide) (Polyline.L.uniform c) (Polyline.L.uniform d)).walls.map _
    rw [Polyline.L.walls_eq 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b) (Polyline.L.uniform c) (Polyline.L.uniform d)]
  · change ((Out.atlas 99970 98979 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).walls.map _).map _=
      ((Out.atlas 99970 98979 (by decide) (by decide) (Polyline.L.uniform c) (Polyline.L.uniform d)).walls.map _).map _
    rw [Out.walls_eq 99970 98979 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b) (Polyline.L.uniform c) (Polyline.L.uniform d)]
  · change (((In.atlas 98981 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).walls.map _).map _).map _=
      (((In.atlas 98981 99969 (by decide) (by decide) (Polyline.L.uniform c) (Polyline.L.uniform d)).walls.map _).map _).map _
    rw [In.walls_eq 98981 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b) (Polyline.L.uniform c) (Polyline.L.uniform d)]
  · change ((((Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).walls.map _).map _).map _).map _=
      ((((Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform c) (Polyline.L.uniform d)).walls.map _).map _).map _).map _
    rw [Polyline.L.walls_eq 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b) (Polyline.L.uniform c) (Polyline.L.uniform d)]

theorem puzzle_walls_eq (k : Kind) (a b c d : Bool) :
    @Eq (Finset Cell) (puzzle k a b).board.walls (puzzle k c d).board.walls := walls_eq k a b c d

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
