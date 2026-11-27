/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombTourDarts
public import PushS.CombCrossingRotation
import all PushS.CombCrossingRotation
public import PushS.CombNativeRotation
public import PushS.PermutationWalkWord
import all PushS.CombStationDarts
import all PushS.CombDarts
import all PushS.CombGenus

/-! The literal ascending and descending walks use exactly the actual native tooth pieces and source-side occurrences. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

section Geometry

variable (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
  (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin G.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))

/-- The literal ascending actual tooth pieces alternate with their original left source occurrences. -/
@[expose] def toothAscent (vertex : Fin d.1.length) : List (Graph.Dart (augmentedGraph width hd)) :=
  PushPuzzle.List.alternatingWalk (fun piece => (Piece.tooth vertex piece).dart width hd false)
    (fun hit => crossingDart width hd (toothCrossingHit width d vertex hit) false)

/-- The literal descending actual tooth pieces alternate with their original right source occurrences. -/
@[expose] def toothDescent (vertex : Fin d.1.length) : List (Graph.Dart (augmentedGraph width hd)) :=
  (PushPuzzle.List.alternatingWalk (fun piece => (Piece.tooth vertex piece).dart width hd true)
    (fun hit => crossingDart width hd (toothCrossingHit width d vertex hit) true)).reverse

include hfit in
/-- The indexed actual tooth encounter names exactly its original adjacent up or down piece. -/
theorem toothCrossingDart_hit (vertex : Fin d.1.length) (hit : Fin (toothCrossings width d vertex).length) (upward : Bool) :
    (Piece.tooth vertex (if upward then hit.succ else hit.castSucc)).dart width hd (!upward) =
      toothCrossingDart width hd (toothCrossingHit width d vertex hit) upward := by
  cases upward
  · exact tooth_dart_crossing width height hd hfit vertex hit.castSucc true _
      (by simpa only [ite_true, Fin.succ_castSucc] using toothStation_crossing width d vertex hit)
  · exact tooth_dart_crossing width height hd hfit vertex hit.succ false _
      (by simpa only [Bool.false_eq_true, ite_false] using toothStation_crossing width d vertex hit)

/-- An actual upward tooth piece next reaches its own original ascending source side. -/
theorem toothTour_up_to_source (vertex : Fin d.1.length) (hit : Fin (toothCrossings width d vertex).length) :
    (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length
      ((Piece.tooth vertex hit.castSucc).dart width hd false) = crossingDart width hd (toothCrossingHit width d vertex hit) false := by
  rw [Piece.treeTour_dart]
  change (augmentedRotation width height hd hfit hhead).rotate ((Piece.tooth vertex hit.castSucc).dart width hd true) = _
  have he := toothCrossingDart_hit width height hd hfit vertex hit false
  simp only [Bool.false_eq_true, ite_false, Bool.not_false] at he
  rw [he]
  exact augmentedRotation_crossing width height hd hfit hhead _ 0

/-- After that original ascending source side, the actual tour follows its next upward tooth piece. -/
theorem toothTour_source_to_up (vertex : Fin d.1.length) (hit : Fin (toothCrossings width d vertex).length) :
    (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length
      (crossingDart width hd (toothCrossingHit width d vertex hit) false) = (Piece.tooth vertex hit.succ).dart width hd false := by
  rw [treeTour_source_dart width hd _ _ _ (crossingDart_token width hd _ false)]
  have he := toothCrossingDart_hit width height hd hfit vertex hit true
  simp only [ite_true, Bool.not_true] at he
  rw [he]
  exact augmentedRotation_crossing width height hd hfit hhead _ 1

/-- A descending actual tooth piece next reaches its original returning source side. -/
theorem toothTour_down_to_source (vertex : Fin d.1.length) (hit : Fin (toothCrossings width d vertex).length) :
    (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length
      ((Piece.tooth vertex hit.succ).dart width hd true) = crossingDart width hd (toothCrossingHit width d vertex hit) true := by
  rw [Piece.treeTour_dart]
  change (augmentedRotation width height hd hfit hhead).rotate ((Piece.tooth vertex hit.succ).dart width hd false) = _
  have he := toothCrossingDart_hit width height hd hfit vertex hit true
  simp only [ite_true, Bool.not_true] at he
  rw [he]
  exact augmentedRotation_crossing width height hd hfit hhead _ 2

/-- After that original returning source side, the actual tour follows its preceding downward tooth piece. -/
theorem toothTour_source_to_down (vertex : Fin d.1.length) (hit : Fin (toothCrossings width d vertex).length) :
    (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length
      (crossingDart width hd (toothCrossingHit width d vertex hit) true) = (Piece.tooth vertex hit.castSucc).dart width hd true := by
  rw [treeTour_source_dart width hd _ _ _ (crossingDart_token width hd _ true)]
  have he := toothCrossingDart_hit width height hd hfit vertex hit false
  simp only [Bool.false_eq_true, ite_false, Bool.not_false] at he
  rw [he]
  exact augmentedRotation_crossing width height hd hfit hhead _ 3

/-- The entire literal upward word is the same genuine tree-tour chain to the final native-tip approach. -/
theorem toothAscent_chain (vertex : Fin d.1.length) :
    (toothAscent width hd vertex).IsChainFromTo
      (fun a b => (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length a = b)
      (toothFootDart width hd vertex)
      ((Piece.tooth vertex (Fin.last (toothCrossings width d vertex).length)).dart width hd false) :=
  PushPuzzle.List.alternatingWalk_isChainFromTo _ _ (toothTour_up_to_source width height hd hfit hhead vertex)
    (toothTour_source_to_up width height hd hfit hhead vertex)

/-- The entire literal return word is the same genuine tree-tour chain down to the original lower foot. -/
theorem toothDescent_chain (vertex : Fin d.1.length) :
    (toothDescent width hd vertex).IsChainFromTo
      (fun a b => (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length a = b)
      (toothTipDart width hd vertex) ((Piece.tooth vertex 0).dart width hd true) := by
  have h := PushPuzzle.List.alternatingWalk_isChainFromTo (r := fun a b =>
    (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length b = a)
    (fun piece => (Piece.tooth vertex piece).dart width hd true)
    (fun hit => crossingDart width hd (toothCrossingHit width d vertex hit) true)
    (toothTour_source_to_down width height hd hfit hhead vertex) (toothTour_down_to_source width height hd hfit hhead vertex)
  exact (PushPuzzle.List.IsChainFromTo.reverse_chain h)

/-- Each actual one-way tooth contour retains one end per piece and one original source occurrence per crossing. -/
theorem toothAscent_length (vertex : Fin d.1.length) :
    (toothAscent width hd vertex).length = 2 * (toothCrossings width d vertex).length + 1 := PushPuzzle.List.alternatingWalk_length _ _

/-- The actual returning tooth contour has the same exact number of original occurrences. -/
theorem toothDescent_length (vertex : Fin d.1.length) :
    (toothDescent width hd vertex).length = 2 * (toothCrossings width d vertex).length + 1 := by
  rw [toothDescent, List.length_reverse, PushPuzzle.List.alternatingWalk_length]

end Geometry
end PushPuzzle.PushS.Comb
