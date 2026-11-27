/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Diagram.Word.TraceData
public import PushS.Source.Strip.PolyTime.Incidence
public import PushS.Source.Planar.GridDrawing.WindowPath
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary

/-!
# Standard encoded native edge windows of the actual word drawing

Scan the same compiled native graph for each original ordered incidence. Its original native
vertex index reads the already computed canonical center. Translate the finite edge window to
that actual false endpoint's row, and populate it with the exact original native trace queries.

## Main definitions

* `PushPuzzle.NCL.Word.DrawingData.EdgeInput`: same original word and same native creation-order edge label.
* `PushPuzzle.NCL.Word.DrawingData.EdgeInput.pattern`: original endpoint/trace data in the fixed edge window.

## Main results

* `PushPuzzle.NCL.Word.DrawingData.EdgeInput.computableInPolyTime_pattern`: standard finite-window emission.
-/

public section

namespace PushPuzzle.NCL.Word.DrawingData

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Word Cslib _root_.Turing.MultiTapeTM

/-- An original structurally encoded word and one original native creation-order edge label. -/
structure EdgeInput where
  /-- The same original primitive word. -/
  word : Word
  /-- The same original native edge label. -/
  edge : ℕ

/-- Original structural word and unary native edge label. -/
enc_structure encEdgeInput : EdgeInput where word : encWord, edge : encUnary

/-- Original native edge input paired with its original reference-direction tag. -/
abbrev encEdgeSide := encPair encEdgeInput encBool

/-- Scan the original native graph's original vertex order for the indicated incidence. -/
@[expose] def EdgeInput.endpoint (input : EdgeInput) (dir : Bool) : ℕ :=
  PushPuzzle.NCL.Strip.PolyTime.endpointIndex input.word.compile.vertices ⟨input.edge, dir⟩

/-- The original nonnegative canonical center of that same original incidence. -/
@[expose] def EdgeInput.position (input : EdgeInput) (dir : Bool) : GridRouting.Point :=
  gridPositionAt input.word (input.endpoint dir)

/-- Read the same original native endpoint vertex in standard polynomial time. -/
private theorem EdgeInput.computableInPolyTime_endpoint :
    ComputableInPolyTime (fun p : EdgeInput × Bool => p.1.endpoint p.2) encEdgeSide encUnary := by
  have hg := Word.computableInPolyTime_compile.comp
    (encEdgeInput_word_polyTime (ComputableInPolyTime.fst encEdgeInput encBool))
  have hv := encAndOrGraph_vertices_polyTime hg
  have he : ComputableInPolyTime (fun p : EdgeInput × Bool => p.1.edge)
      encEdgeSide encNat :=
    ComputableInPolyTime.unary_to_binary.comp
      (encEdgeInput_edge_polyTime (ComputableInPolyTime.fst encEdgeInput encBool))
  have hp : ComputableInPolyTime (fun p : EdgeInput × Bool => (⟨p.1.edge, p.2⟩ : Port ℕ))
      encEdgeSide (encPort encNat) := by fun_prop
  exact (PushPuzzle.NCL.Strip.PolyTime.computableInPolyTime_endpointIndex.comp (hv.prod hp)).of_enc_eq
    (fun _ => rfl)

/-- The original endpoint center emits in standard unary nonnegative grid coordinates. -/
theorem EdgeInput.computableInPolyTime_position :
    ComputableInPolyTime (fun p : EdgeInput × Bool => p.1.position p.2)
      encEdgeSide encGridPoint := by
  have hi : ComputableInPolyTime (fun p : EdgeInput × Bool => (p.1.word, p.1.endpoint p.2))
      encEdgeSide encQuery := by
    exact (encEdgeInput_word_polyTime (ComputableInPolyTime.fst encEdgeInput encBool)).prod
      PushPuzzle.NCL.Word.DrawingData.EdgeInput.computableInPolyTime_endpoint
  exact (computableInPolyTime_gridPositionAt.comp hi).of_enc_eq (fun _ => rfl)

private def tag (bound n : ℕ) : Fin (bound + 1) := (List.finRange (bound + 1)).getD n 0

private theorem computableInPolyTime_tag (bound : ℕ) :
    ComputableInPolyTime (tag bound) encUnary (encFinEnum (Fin (bound + 1))) :=
  ComputableInPolyTime.listGetDWithInput (ComputableInPolyTime.const _)
    ComputableInPolyTime.id' 0

/-- The same actual native edge's translated finite endpoint and trace table. -/
def EdgeInput.pattern (width span : ℕ) (input : EdgeInput) :
    PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern (Strip.Sweep.drawingWidth width) span where
  source := (tag (Strip.Sweep.drawingWidth width) (input.position false).1, 0)
  target := (tag (Strip.Sweep.drawingWidth width) (input.position true).1,
    tag span ((input.position true).2 - (input.position false).2))
  marked x y := (PushPuzzle.NCL.Word.DrawingData.TraceInput.mk input.word input.edge x.val
    ((input.position false).2 + y.val)).trace width

private theorem computableInPolyTime_side (dir : Bool) :
    ComputableInPolyTime (fun input : EdgeInput => input.position dir) encEdgeInput encGridPoint :=
  (PushPuzzle.NCL.Word.DrawingData.EdgeInput.computableInPolyTime_position.comp
    (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const dir))).of_enc_eq (fun _ => rfl)

private theorem computableInPolyTime_mask (width span : ℕ) :
    ComputableInPolyTime (fun input : EdgeInput => (input.pattern width span).marked)
      encEdgeInput
      (encFinFn (Strip.Sweep.drawingWidth width + 1) (encFinFn (span + 1) encBool)) := by
  apply ComputableInPolyTime.finFn
  intro x
  apply ComputableInPolyTime.finFn
  intro y
  have hs := computableInPolyTime_side false
  have hsy : ComputableInPolyTime (fun input : EdgeInput => (input.position false).2)
      encEdgeInput encUnary := hs.snd'
  have hi : ComputableInPolyTime (fun input : EdgeInput => PushPuzzle.NCL.Word.DrawingData.TraceInput.mk input.word input.edge
      x.val ((input.position false).2 + y.val)) encEdgeInput encTraceInput := by
    apply encTraceInput_mk_polyTime <;> fun_prop
  exact ((PushPuzzle.NCL.Word.DrawingData.TraceInput.computableInPolyTime_trace width).comp hi).of_enc_eq (fun _ => rfl)

/-- The same actual original native edge's finite window table emits in polynomial time. -/
theorem EdgeInput.computableInPolyTime_pattern (width span : ℕ) :
    ComputableInPolyTime (PushPuzzle.NCL.Word.DrawingData.EdgeInput.pattern width span) encEdgeInput
      (PushPuzzle.NCL.GridDrawing.WindowRoute.encPattern (Strip.Sweep.drawingWidth width) span) := by
  have hs := computableInPolyTime_side false
  have ht := computableInPolyTime_side true
  have htag := computableInPolyTime_tag (Strip.Sweep.drawingWidth width)
  have hspan := computableInPolyTime_tag span
  have hsource : ComputableInPolyTime (fun input : EdgeInput => (input.pattern width span).source)
      encEdgeInput (PushPuzzle.NCL.GridDrawing.WindowRoute.encPoint (Strip.Sweep.drawingWidth width) span) := by
    change ComputableInPolyTime (fun input : EdgeInput =>
      (tag (Strip.Sweep.drawingWidth width) (input.position false).1, 0)) _ _
    fun_prop
  have htarget : ComputableInPolyTime (fun input : EdgeInput => (input.pattern width span).target)
      encEdgeInput (PushPuzzle.NCL.GridDrawing.WindowRoute.encPoint (Strip.Sweep.drawingWidth width) span) := by
    change ComputableInPolyTime (fun input : EdgeInput =>
      (tag (Strip.Sweep.drawingWidth width) (input.position true).1,
        tag span ((input.position true).2 - (input.position false).2))) _ _
    fun_prop
  exact PushPuzzle.NCL.GridDrawing.WindowRoute.encPattern_mk_polyTime (Strip.Sweep.drawingWidth width) span
    hsource htarget (computableInPolyTime_mask width span)

end PushPuzzle.NCL.Word.DrawingData
