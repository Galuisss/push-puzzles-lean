/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombRetainedTokens
public import PushS.CombTourInventory
import all PushS.CombTourWord
import all PushS.CombRootedTour
import all PushS.CombContraction

/-! Genuine tree contraction retains exactly the original source contour as its indexed loop rotation word. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

section Native

variable (width : ℕ) {g : NCL.AndOrGraph} (hg : NCL.SourceValid g) (drawing : NCL.GridDrawing.Closed g.graph)
  {d : Graph.OrthogonalDrawing} (hd : drawing.incidenceGraph.IsPlanarOrthogonalDrawing d) (hv : 0 < d.1.length)
  (height : ℕ) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin drawing.incidenceGraph.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition drawing.incidenceGraph d drawing.incidenceGraph.edges[edge].1))

/-- The same actual augmented tree tour is exactly the complete original native comb word's permutation. -/
theorem combTourWord_formPerm :
    (PushPuzzle.Graph.RotationSystem.treeTour (augmentedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length =
      (combTourWord width hg drawing hd hv).formPerm := by
  obtain ⟨last, hchain, hclose⟩ := combTourWord_closed width hg drawing hd hv height hfit hhead
  exact PushPuzzle.List.IsChainFromTo.perm_eq_formPerm _ hchain hclose (combTourWord_nodup width hg drawing hd hv) (combTourWord_cover width hg drawing hd hv)

include hg in
/-- The actual contracted rotation retains the same source-word order and every original fragment end token. -/
theorem contractedRotation_source_word : ∃ word : List (Graph.Dart (contractedGraph width hd hv)), word.Nodup ∧
    (contractedRotation width height hd hfit hhead hv).rotate = word.formPerm ∧
      word.map (retainedToken width hd hv) = sourceOrder width ⟨g, d⟩ := by
  let original := combTourWord width hg drawing hd hv
  let rootedWord := original.map (rootedDartEquiv width hd).symm
  have hn : rootedWord.Nodup := (combTourWord_nodup width hg drawing hd hv).map (rootedDartEquiv width hd).symm.injective
  have hword := rootedRotation_treeTour_word width height hd hfit hhead original
    (combTourWord_formPerm width hg drawing hd hv height hfit hhead)
  obtain ⟨word, hnodup, hrotation, hcoordinates⟩ := contractedRotation_word width height hd hfit hhead hv rootedWord hn hword
  refine ⟨word, hnodup, hrotation, ?_⟩
  have hread := congrArg (fun coordinates => coordinates.filterMap (sourceCoordinateToken width hd)) hcoordinates
  rw [retainedToken_word, sourceCoordinateToken_filter, rootedToken_word] at hread
  exact hread.trans (combTourWord_readout width hg drawing hd hv)

end Native
end PushPuzzle.PushS.Comb
