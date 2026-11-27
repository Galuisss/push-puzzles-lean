/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombNativeToothWord
public import PushS.CombFootRotation
import all PushS.CombDarts
import all PushS.CombSpineDarts
import all PushS.CombFootRotation
import all PushS.CombGenus

/-! The actual spine joins successive complete native tooth walks and its literal returning sequence. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

section Geometry

variable (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
  (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin G.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))

/-- The indexed rightward spine piece is exactly the canonical successor dart at its left foot. -/
theorem spineRightDart_piece (piece : Fin (d.1.length - 1)) :
    spineRightDart width hd (spineLeft width d piece) (by rw [spineLeft_rank]; have := piece.isLt; omega) =
      (Piece.spine piece).dart width hd false := by
  unfold spineRightDart
  congr 2
  exact Fin.ext (spineLeft_rank width d piece)

/-- The indexed leftward spine piece is exactly the canonical predecessor dart at its right foot. -/
theorem spineLeftDart_piece (piece : Fin (d.1.length - 1)) :
    spineLeftDart width hd (spineRight width d piece) (by rw [spineRight_rank]; omega) =
      (Piece.spine piece).dart width hd true := by
  unfold spineLeftDart
  congr 2
  apply Fin.ext
  change vertexRank width d (spineRight width d piece) - 1 = piece.val
  rw [spineRight_rank]
  omega

/-- A complete native tooth word continues along the exact next indexed spine piece. -/
theorem toothTour_to_spine (piece : Fin (d.1.length - 1)) :
    (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length
      ((Piece.tooth (spineLeft width d piece) 0).dart width hd true) = (Piece.spine piece).dart width hd false := by
  rw [Piece.treeTour_dart]
  have h := augmentedRotation_toothFoot_right width height hd hfit hhead (spineLeft width d piece)
    (by rw [spineLeft_rank]; have := piece.isLt; omega)
  rw [spineRightDart_piece] at h
  exact h

/-- The exact original forward spine piece enters the next native tooth word. -/
theorem spineTour_to_tooth (piece : Fin (d.1.length - 1)) :
    (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length
      ((Piece.spine piece).dart width hd false) = toothFootDart width hd (spineRight width d piece) := by
  rw [Piece.treeTour_dart]
  have h := augmentedRotation_spineLeft width height hd hfit hhead (spineRight width d piece) (by rw [spineRight_rank]; omega)
  rw [spineLeftDart_piece] at h
  exact h

/-- Returning along any later actual spine piece continues to the exact previous indexed piece. -/
theorem spineTour_return (piece : Fin (d.1.length - 1)) (hpos : 0 < piece.val) :
    (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length
      ((Piece.spine piece).dart width hd true) = (Piece.spine ⟨piece.val - 1, by have := piece.isLt; omega⟩).dart width hd true := by
  rw [Piece.treeTour_dart]
  change (augmentedRotation width height hd hfit hhead).rotate ((Piece.spine piece).dart width hd false) = _
  have h := augmentedRotation_spineRight_left width height hd hfit hhead (spineLeft width d piece)
    (by rw [spineLeft_rank]; exact hpos) (by rw [spineLeft_rank]; have := piece.isLt; omega)
  rw [spineRightDart_piece] at h
  have he : spineLeftDart width hd (spineLeft width d piece) (by rw [spineLeft_rank]; exact hpos) =
      (Piece.spine ⟨piece.val - 1, by have := piece.isLt; omega⟩).dart width hd true := by
    unfold spineLeftDart
    congr 2
    apply Fin.ext
    change vertexRank width d (spineLeft width d piece) - 1 = piece.val - 1
    rw [spineLeft_rank]
  exact h.trans he

/-- The first actual returning spine piece closes the tour at the original first tooth. -/
theorem spineTour_first (hvertices : 1 < d.1.length) :
    (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length
      ((Piece.spine ⟨0, by omega⟩).dart width hd true) = toothFootDart width hd (spineVertex width d ⟨0, by omega⟩) := by
  rw [Piece.treeTour_dart]
  have h := augmentedRotation_spineRight_first width height hd hfit hhead (spineLeft width d ⟨0, by omega⟩)
    (by rw [spineLeft_rank]; change ¬ 0 < (0 : ℕ); omega) (by rw [spineLeft_rank]; change 0 + 1 < d.1.length; omega)
  rw [spineRightDart_piece] at h
  exact h

end Geometry
end PushPuzzle.PushS.Comb
