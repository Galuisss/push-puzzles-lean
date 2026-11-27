/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombSpineTour
public import PushS.PermutationBlockWalk
public import Mathlib.Data.List.ChainOfFn
import all PushS.CombSpineTour
import all PushS.CombNativeToothWord
import all PushS.CombFootRotation
import all PushS.CombGenus
import all PushS.CombDarts

/-! The actual full comb contour concatenates original native tooth words along the indexed spine and back. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- The actual source vertex at one literal full comb-walk position. -/
@[expose] def tourVertex (width : ℕ) (d : Graph.OrthogonalDrawing) (hv : 0 < d.1.length)
    (index : Fin (d.1.length - 1 + 1)) : Fin d.1.length :=
  spineVertex width d ⟨index.val, by have := index.isLt; omega⟩

section Native

variable (width : ℕ) {g : NCL.AndOrGraph} (hg : NCL.SourceValid g) (drawing : NCL.GridDrawing.Closed g.graph)
  {d : Graph.OrthogonalDrawing} (hd : drawing.incidenceGraph.IsPlanarOrthogonalDrawing d) (hv : 0 < d.1.length)

/-- The actual forward contour reads every original native tooth in literal spine order. -/
@[expose] def combForwardWord : List (Graph.Dart (augmentedGraph width hd)) :=
  PushPuzzle.List.blockWalk (fun index => nativeToothWord width hg drawing hd (tourVertex width d hv index))
    (fun piece => (Piece.spine piece).dart width hd false)

/-- The return contour follows exactly the actual spine pieces in reverse original order. -/
@[expose] def combReturnWord : List (Graph.Dart (augmentedGraph width hd)) :=
  (List.ofFn fun piece => (Piece.spine piece).dart width hd true).reverse

/-- The complete original comb tour word on genuine indexed source and auxiliary darts. -/
@[expose] def combTourWord : List (Graph.Dart (augmentedGraph width hd)) :=
  combForwardWord width hg drawing hd hv ++ combReturnWord width drawing hd

section Geometry

variable (height : ℕ) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin drawing.incidenceGraph.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition drawing.incidenceGraph d drawing.incidenceGraph.edges[edge].1))

/-- The complete literal forward comb word is its actual geometric tree-tour chain. -/
theorem combForwardWord_chain :
    (combForwardWord width hg drawing hd hv).IsChainFromTo
      (fun a b => (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length a = b)
      (toothFootDart width hd (tourVertex width d hv 0))
      ((Piece.tooth (tourVertex width d hv (Fin.last (d.1.length - 1))) 0).dart width hd true) := by
  apply PushPuzzle.List.blockWalk_isChainFromTo _ _ _ _ (fun index => nativeToothWord_chain width hg drawing hd height hfit hhead _)
  · intro piece
    exact toothTour_to_spine width height hd hfit hhead piece
  · intro piece
    exact spineTour_to_tooth width height hd hfit hhead piece

private theorem spine_forward_return_chain (hvertices : 1 < d.1.length) :
    (List.ofFn fun piece : Fin (d.1.length - 1) => (Piece.spine piece).dart width hd true).IsChainFromTo
      (fun a b => (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length b = a)
      ((Piece.spine ⟨0, by omega⟩).dart width hd true)
      ((Piece.spine ⟨d.1.length - 2, by omega⟩).dart width hd true) := by
  refine ⟨List.isChain_ofFn.mpr ?_, by apply List.ne_nil_of_length_pos; rw [List.length_ofFn]; omega, ?_, ?_⟩
  · intro index hi
    have h := spineTour_return width height hd hfit hhead ⟨index + 1, hi⟩ (by change 0 < index + 1; omega)
    simpa only [Nat.add_sub_cancel] using h
  · simp only [List.head_ofFn]
  · simp only [List.getLast_ofFn]
    congr 2

/-- The entire literal reverse-spine word is the same actual geometric tree-tour chain. -/
theorem combReturnWord_chain (hvertices : 1 < d.1.length) :
    (combReturnWord width drawing hd).IsChainFromTo
      (fun a b => (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length a = b)
      ((Piece.spine ⟨d.1.length - 2, by omega⟩).dart width hd true)
      ((Piece.spine ⟨0, by omega⟩).dart width hd true) :=
  (PushPuzzle.List.IsChainFromTo.reverse_chain (spine_forward_return_chain width drawing hd height hfit hhead hvertices))

private theorem last_tooth_to_return (hvertices : 1 < d.1.length) :
    (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length
      ((Piece.tooth (tourVertex width d hv (Fin.last (d.1.length - 1))) 0).dart width hd true) =
      (Piece.spine ⟨d.1.length - 2, by omega⟩).dart width hd true := by
  let vertex := tourVertex width d hv (Fin.last (d.1.length - 1))
  have hrank : vertexRank width d vertex = d.1.length - 1 :=
    congrArg Fin.val (spineRank_spineVertex width d ⟨d.1.length - 1, by omega⟩)
  have hl : 0 < vertexRank width d vertex := by rw [hrank]; omega
  have hr : ¬ vertexRank width d vertex + 1 < d.1.length := by rw [hrank]; omega
  rw [Piece.treeTour_dart]
  change (augmentedRotation width height hd hfit hhead).rotate (toothFootDart width hd vertex) = _
  have h := augmentedRotation_toothFoot_left width height hd hfit hhead vertex hl hr
  apply h.trans
  unfold spineLeftDart
  congr 2
  apply Fin.ext
  change vertexRank width d vertex - 1 = d.1.length - 2
  rw [hrank]
  omega

/-- The entire original comb contour is a closed actual tree-tour chain, including the one-vertex case. -/
theorem combTourWord_closed : ∃ last : Graph.Dart (augmentedGraph width hd),
    (combTourWord width hg drawing hd hv).IsChainFromTo
      (fun a b => (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length a = b)
      (toothFootDart width hd (tourVertex width d hv 0)) last ∧
    (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length last =
      toothFootDart width hd (tourVertex width d hv 0) := by
  by_cases hvertices : 1 < d.1.length
  · refine ⟨(Piece.spine ⟨0, by omega⟩).dart width hd true, ?_, ?_⟩
    · exact (PushPuzzle.List.IsChainFromTo.append_step (combForwardWord_chain width hg drawing hd hv height hfit hhead))
        (combReturnWord_chain width drawing hd height hfit hhead hvertices)
        (last_tooth_to_return width drawing hd hv height hfit hhead hvertices)
    · exact spineTour_first width height hd hfit hhead hvertices
  · have hlen : d.1.length = 1 := by omega
    have hempty : combReturnWord width drawing hd = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp only [combReturnWord, List.length_reverse, List.length_ofFn]
      omega
    have hlast : Fin.last (d.1.length - 1) = (0 : Fin (d.1.length - 1 + 1)) := by
      apply Fin.ext
      change d.1.length - 1 = 0
      omega
    refine ⟨(Piece.tooth (tourVertex width d hv 0) 0).dart width hd true, ?_, ?_⟩
    · have h := combForwardWord_chain width hg drawing hd hv height hfit hhead
      rw [hlast] at h
      simpa only [combTourWord, hempty, List.append_nil] using h
    · rw [Piece.treeTour_dart]
      have hrank := vertexRank_lt width d (tourVertex width d hv 0).isLt
      exact augmentedRotation_toothFoot_single width height hd hfit hhead _ (by omega) (by omega)

end Geometry
end Native
end PushPuzzle.PushS.Comb
