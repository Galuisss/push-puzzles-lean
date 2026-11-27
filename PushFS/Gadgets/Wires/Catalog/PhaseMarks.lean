/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.PhaseWalls

/-! Exact complete unlabelled canonical box and goal sets of ordinary physical glyphs. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog


open Reduction
set_option maxRecDepth 65536

private theorem placed_boxset {I : Instance} {L : Type} [Fintype L] {W H : ℕ}
    (M : SlotMatching I L) (dx dy : ℕ) (hx : dx+I.width≤W) (hy : dy+I.height≤H) :
    (placedAtlas M dx dy hx hy).initial.boxes=I.initial.boxes.map (GridEmbedding.translate dx dy hx hy).cells := by
  have hh := congrArg State.boxes (placed_initial M dx dy hx hy)
  simpa only [GridEmbedding.extend,Finset.union_empty] using hh

theorem initial_retarget (k : Kind) (a b c : Bool) :
    @Eq (Finset Cell) (puzzle k a b).initial.boxes (puzzle k a c).initial.boxes := by
  change (placedAtlas (baseMatching k a b) (dx k) (dy k) (fitsX k a b) (fitsY k a b)).initial.boxes=
    (placedAtlas (baseMatching k a c) (dx k) (dy k) (fitsX k a c) (fitsY k a c)).initial.boxes
  rw [placed_boxset,placed_boxset]
  cases k
  all_goals dsimp only [base,Instance.reflectedX,Instance.transposed,GridIsometry.reorientInstance,
    GridIsometry.state,StorageAtlas.puzzle,Chain.puzzle,Chain.state,dx,dy]
  · rw [Polyline.L.initial_boxes,Polyline.L.initial_boxes]
  · rw [Out.initial_boxes,Out.initial_boxes]
  · rw [In.initial_boxes,In.initial_boxes]
  · rw [Polyline.L.initial_boxes,Polyline.L.initial_boxes]

theorem goals_canonical (k : Kind) (a b : Bool) :
    @Eq (Finset Cell) (puzzle k a b).board.goals (puzzle k b b).initial.boxes := by
  change (placedAtlas (baseMatching k a b) (dx k) (dy k) (fitsX k a b) (fitsY k a b)).board.goals=
    (placedAtlas (baseMatching k b b) (dx k) (dy k) (fitsX k b b) (fitsY k b b)).initial.boxes
  rw [placed_goals,placed_boxset]
  cases k
  all_goals dsimp only [base,Instance.reflectedX,Instance.transposed,GridIsometry.reorientInstance,
    GridIsometry.board,GridIsometry.state,StorageAtlas.puzzle,Chain.puzzle,Chain.board,Chain.state,dx,dy]
  · rw [Polyline.L.goals_eq,Polyline.L.initial_boxes]
  · rw [Out.goals_eq,Out.initial_boxes]
  · rw [In.goals_eq,In.initial_boxes]
  · rw [Polyline.L.goals_eq,Polyline.L.initial_boxes]

theorem goals_reinitial (k : Kind) (a c b : Bool) :
    @Eq (Finset Cell) (puzzle k a b).board.goals (puzzle k c b).board.goals :=
  (goals_canonical k a b).trans (goals_canonical k c b).symm

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
