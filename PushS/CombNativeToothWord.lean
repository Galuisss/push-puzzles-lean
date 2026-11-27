/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombToothTour
import all PushS.CombToothTour
import all PushS.CombNativeRotation
import all PushS.CombNativeFanDarts
import all PushS.CombGenus
import all PushS.CombDarts

/-! Each complete actual native tooth walk includes its original sorted three-port fan. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

section Native

variable (width : ℕ) {g : NCL.AndOrGraph} (hg : NCL.SourceValid g) (drawing : NCL.GridDrawing.Closed g.graph)
  {d : Graph.OrthogonalDrawing} (hd : drawing.incidenceGraph.IsPlanarOrthogonalDrawing d)

/-- The entire actual tooth contour, retaining every original source occurrence and auxiliary tree dart. -/
@[expose] def nativeToothWord (vertex : Fin d.1.length) : List (Graph.Dart (augmentedGraph width hd)) :=
  toothAscent width hd vertex ++ List.ofFn (nativeFanDart width hg drawing hd vertex) ++ toothDescent width hd vertex

/-- A complete actual native tooth contributes precisely its four crossing visits and five fixed end visits. -/
theorem nativeToothWord_length (vertex : Fin d.1.length) :
    (nativeToothWord width hg drawing hd vertex).length = 4 * (toothCrossings width d vertex).length + 5 := by
  simp only [nativeToothWord, List.length_append, toothAscent_length, toothDescent_length, List.length_ofFn]
  omega

section Geometry

variable (height : ℕ) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin drawing.incidenceGraph.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition drawing.incidenceGraph d drawing.incidenceGraph.edges[edge].1))

private theorem nativeFan_tour_step (vertex : Fin d.1.length) (slot : Fin 2) :
    (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length
      (nativeFanDart width hg drawing hd vertex slot.castSucc) = nativeFanDart width hg drawing hd vertex slot.succ := by
  rw [treeTour_source_dart width hd _ _ _ (nativeFanDart_token width hg drawing hd vertex slot.castSucc)]
  fin_cases slot
  · exact augmentedRotation_native width hg drawing hd height hfit hhead vertex 1
  · exact augmentedRotation_native width hg drawing hd height hfit hhead vertex 2

private theorem nativeFan_word_chain (vertex : Fin d.1.length) :
    (List.ofFn (nativeFanDart width hg drawing hd vertex)).IsChainFromTo
      (fun a b => (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length a = b)
      (nativeFanDart width hg drawing hd vertex 0) (nativeFanDart width hg drawing hd vertex 2) := by
  have hs : [nativeFanDart width hg drawing hd vertex 2].IsChainFromTo
      (fun a b => (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length a = b)
      (nativeFanDart width hg drawing hd vertex 2) (nativeFanDart width hg drawing hd vertex 2) := List.isChainFromTo_singleton
  exact (hs.cons (r := fun a b => (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length a = b)
    (nativeFan_tour_step width hg drawing hd height hfit hhead vertex 1)).cons
      (r := fun a b => (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length a = b)
      (nativeFan_tour_step width hg drawing hd height hfit hhead vertex 0)

/-- The last upward tooth piece reaches precisely the first original weighted fan slot. -/
theorem toothTour_up_to_fan (vertex : Fin d.1.length) :
    (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length
      ((Piece.tooth vertex (Fin.last (toothCrossings width d vertex).length)).dart width hd false) =
      nativeFanDart width hg drawing hd vertex 0 := by
  rw [Piece.treeTour_dart]
  exact augmentedRotation_native width hg drawing hd height hfit hhead vertex 0

/-- The final original weighted fan slot reaches precisely the downward native-tip tooth dart. -/
theorem toothTour_fan_to_down (vertex : Fin d.1.length) :
    (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length
      (nativeFanDart width hg drawing hd vertex 2) = toothTipDart width hd vertex := by
  rw [treeTour_source_dart width hd _ _ _ (nativeFanDart_token width hg drawing hd vertex 2)]
  exact augmentedRotation_native width hg drawing hd height hfit hhead vertex 3

/-- The complete literal native tooth word is a genuine actual tree-tour chain from and back toward its lower foot. -/
theorem nativeToothWord_chain (vertex : Fin d.1.length) :
    (nativeToothWord width hg drawing hd vertex).IsChainFromTo
      (fun a b => (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length a = b)
      (toothFootDart width hd vertex) ((Piece.tooth vertex 0).dart width hd true) := by
  exact (PushPuzzle.List.IsChainFromTo.append_step ((PushPuzzle.List.IsChainFromTo.append_step (toothAscent_chain width height hd hfit hhead vertex))
    (nativeFan_word_chain width hg drawing hd height hfit hhead vertex) (toothTour_up_to_fan width hg drawing hd height hfit hhead vertex)))
      (toothDescent_chain width height hd hfit hhead vertex) (toothTour_fan_to_down width hg drawing hd height hfit hhead vertex)

end Geometry
end Native
end PushPuzzle.PushS.Comb
