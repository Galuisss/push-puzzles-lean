/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Diagram.Word.EdgeDrawingData
public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary

/-!
# Standard drawing arrays of the actual native word compiler

For each original creation-order edge, select the downward marked route in its fixed window
and translate it to the original source row. Emit these routes beside the same original native
vertex array.

## Main definitions

* `PushPuzzle.NCL.Word.DrawingData.EdgeInput.route`: selected route at its actual original source row.
* `PushPuzzle.NCL.Word.DrawingData.drawing`: standard native vertex and route arrays.

## Main results

* `PushPuzzle.NCL.Word.DrawingData.computableInPolyTime_drawing`: standard encoded drawing emission.
-/

public section

namespace PushPuzzle.NCL.Word.DrawingData

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Word Cslib _root_.Turing.MultiTapeTM

/-- The selected fixed-window route translated to the original native source row. -/
@[expose] def EdgeInput.route (width span : ℕ) (input : EdgeInput) : Orthogonal.Route :=
  Orthogonal.translate (0, (input.position false).2) (input.pattern width span).integerRoute

/-- The selected actual native edge route emits in standard binary coordinates. -/
private theorem EdgeInput.computableInPolyTime_route (width span : ℕ) :
    ComputableInPolyTime (PushPuzzle.NCL.Word.DrawingData.EdgeInput.route width span) encEdgeInput Orthogonal.encRoute := by
  have hs := PushPuzzle.NCL.Word.DrawingData.EdgeInput.computableInPolyTime_position.comp
    (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const false))
  have hy := (ComputableInPolyTime.intBin_natCast.comp
    ComputableInPolyTime.unary_to_binary).comp hs.snd'
  have ht : ComputableInPolyTime (fun input : EdgeInput =>
      ((0 : ℤ), ((input.position false).2 : ℤ))) encEdgeInput Orthogonal.encPoint := by
    exact (ComputableInPolyTime.const (0 : ℤ)).prod hy
  have hr := (PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.computableInPolyTime_integerRoute
    (Strip.Sweep.drawingWidth width) span).comp (PushPuzzle.NCL.Word.DrawingData.EdgeInput.computableInPolyTime_pattern width span)
  exact (Orthogonal.computableInPolyTime_translate.comp (ht.prod hr)).of_enc_eq (fun _ => rfl)

/-- Selected native edge routes in their original creation order. -/
@[expose] def routes (width span : ℕ) (w : Word) : List Orthogonal.Route :=
  (List.range (Word.run w ⟨[], 0, []⟩).next).map fun edge =>
    (PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w edge).route width span

/-- Actual native vertex positions and selected native edge routes in the standard format. -/
@[expose] def drawing (width span : ℕ) (w : Word) : Graph.OrthogonalDrawing :=
  (vertices w, routes width span w)

/-- The actual original edge count gives a polynomial-time route emission loop. -/
private theorem computableInPolyTime_routes (width span : ℕ) :
    ComputableInPolyTime (routes width span) encWord (encList Orthogonal.encRoute) := by
  have hn := Word.State.computableInPolyTime_next.comp Word.computableInPolyTime_run_empty
  unfold routes
  apply ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn)
  have hi : ComputableInPolyTime (fun p : Word × ℕ => PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk p.1 p.2)
      encQuery encEdgeInput := by
    apply encEdgeInput_mk_polyTime <;> fun_prop
  exact (PushPuzzle.NCL.Word.DrawingData.EdgeInput.computableInPolyTime_route width span).comp hi

/-- Actual native graph drawing arrays emit in standard encoded polynomial time. -/
theorem computableInPolyTime_drawing (width span : ℕ) :
    ComputableInPolyTime (drawing width span) encWord Graph.encOrthogonalDrawing :=
  computableInPolyTime_vertices.prod (computableInPolyTime_routes width span)

end PushPuzzle.NCL.Word.DrawingData
