/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Diagram.Word.LayerTrace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.List.GetD

/-!
# Standard encoded raw inputs to the actual canonical layer trace

The original compiler supplies natural-number shape and slot data. Packing these actual fields
into the fixed finite local query table is standard polynomial-time; each field is retained
exactly throughout its original stated bound.

## Main definitions

* `PushPuzzle.NCL.Word.DrawingData.LayerInput`: original scalar local-layout query fields.
* `PushPuzzle.NCL.Word.DrawingData.LayerInput.pack`: standard finite query-table input.

## Main results

* `PushPuzzle.NCL.Word.DrawingData.LayerInput.computableInPolyTime_test`: standard local trace dispatch.
-/

public section

namespace PushPuzzle.NCL.Word.DrawingData

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Word Cslib _root_.Turing.MultiTapeTM GridLayout

/-- Original scalar layout parameters and one original strand/grid query. -/
structure LayerInput where
  /-- Number of original unchanged suffix wires. -/
  suffix : ℕ
  /-- Original cell offset. -/
  offset : ℕ
  /-- Number of original cell input ports. -/
  inputs : ℕ
  /-- Number of original cell output ports. -/
  outputs : ℕ
  /-- Select an original cell-output slot rather than an incoming-stack slot. -/
  created : Bool
  /-- Original strand slot. -/
  slot : ℕ
  /-- Original local query column. -/
  x : ℕ
  /-- Original local query row. -/
  y : ℕ

/-- Unary original shape, strand slot and grid coordinates, with the original source-side tag. -/
enc_structure encLayerInput : LayerInput where
  suffix : encUnary, offset : encUnary, inputs : encUnary, outputs : encUnary,
  created : encBool, slot : encUnary, x : encUnary, y : encUnary

/-- Retain all original fields in the fixed local layout table's canonical finite slots. -/
@[expose] def LayerInput.pack (width : ℕ) (q : LayerInput) : LayerQuery width :=
  let tag (bound n : ℕ) : Fin (bound + 1) := (List.finRange (bound + 1)).getD n 0
  { suffix := tag width q.suffix
    offset := tag width q.offset
    inputs := tag 3 q.inputs
    outputs := tag 3 q.outputs
    created := q.created
    slot := tag width q.slot
    x := tag (Strip.Sweep.drawingWidth width) q.x
    y := tag (4 * width + 6) q.y }

private theorem computableInPolyTime_tag (bound : ℕ) :
    ComputableInPolyTime (fun n : ℕ => (List.finRange (bound + 1)).getD n 0)
      encUnary (encFinEnum (Fin (bound + 1))) :=
  ComputableInPolyTime.listGetDWithInput (ComputableInPolyTime.const _)
    ComputableInPolyTime.id' 0

/-- Packing the actual scalar input fields into the finite query table is polynomial-time. -/
private theorem LayerInput.computableInPolyTime_pack (width : ℕ) :
    ComputableInPolyTime (PushPuzzle.NCL.Word.DrawingData.LayerInput.pack width) encLayerInput (encLayerQuery width) := by
  have hs := (computableInPolyTime_tag width).comp
    (encLayerInput_suffix_polyTime ComputableInPolyTime.id')
  have hk := (computableInPolyTime_tag width).comp
    (encLayerInput_offset_polyTime ComputableInPolyTime.id')
  have ha := (computableInPolyTime_tag 3).comp
    (encLayerInput_inputs_polyTime ComputableInPolyTime.id')
  have hb := (computableInPolyTime_tag 3).comp
    (encLayerInput_outputs_polyTime ComputableInPolyTime.id')
  have hd := encLayerInput_created_polyTime ComputableInPolyTime.id'
  have hi := (computableInPolyTime_tag width).comp
    (encLayerInput_slot_polyTime ComputableInPolyTime.id')
  have hx := (computableInPolyTime_tag (Strip.Sweep.drawingWidth width)).comp
    (encLayerInput_x_polyTime ComputableInPolyTime.id')
  have hy := (computableInPolyTime_tag (4 * width + 6)).comp
    (encLayerInput_y_polyTime ComputableInPolyTime.id')
  exact encLayerQuery_mk_polyTime width hs hk ha hb hd hi hx hy

/-- Query the original full canonical trace from its original scalar data. -/
@[expose] def LayerInput.test (width : ℕ) (q : LayerInput) : Bool := (q.pack width).test

/-- The same original bounded layer trace dispatches in standard encoded polynomial time. -/
theorem LayerInput.computableInPolyTime_test (width : ℕ) :
    ComputableInPolyTime (PushPuzzle.NCL.Word.DrawingData.LayerInput.test width) encLayerInput encBool :=
  ((PushPuzzle.NCL.Word.DrawingData.LayerQuery.computableInPolyTime_test width).comp
    (PushPuzzle.NCL.Word.DrawingData.LayerInput.computableInPolyTime_pack width)).of_enc_eq (fun _ => rfl)

/-- Erase the finite query bounds while retaining every original layout field. -/
@[expose] def LayerQuery.input {width : ℕ} (q : LayerQuery width) : LayerInput where
  suffix := q.suffix.val
  offset := q.offset.val
  inputs := q.inputs.val
  outputs := q.outputs.val
  created := q.created
  slot := q.slot.val
  x := q.x.val
  y := q.y.val

private theorem tag_fin {bound : ℕ} (i : Fin (bound + 1)) :
    (List.finRange (bound + 1)).getD i.val 0 = i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using i.isLt)]
  simp

/-- Standard packing retains exactly the same original bounded finite query. -/
private theorem LayerQuery.pack_input {width : ℕ}
    (q : LayerQuery width) : q.input.pack width = q := by
  cases q
  dsimp only [PushPuzzle.NCL.Word.DrawingData.LayerQuery.input, PushPuzzle.NCL.Word.DrawingData.LayerInput.pack]
  rw [tag_fin, tag_fin, tag_fin, tag_fin, tag_fin, tag_fin, tag_fin]

/-- Erasing and packing original finite query fields evaluates the same canonical layer trace. -/
private theorem LayerQuery.test_input {width : ℕ} (q : LayerQuery width) :
    q.input.test width = q.test := by
  rw [PushPuzzle.NCL.Word.DrawingData.LayerInput.test, PushPuzzle.NCL.Word.DrawingData.LayerQuery.pack_input]

private theorem input_inputStrand {width k a b r : ℕ} (ha : k + a + r ≤ width)
    (hb : k + b + r ≤ width) (h3 : a + b = 3) (i : Fin (k + a + r))
    (x : Fin (Strip.Sweep.drawingWidth width + 1)) (y : Fin (4 * width + 7)) :
    (PushPuzzle.NCL.Word.DrawingData.LayerQuery.ofStrand ha hb h3 (inputStrand i) x y).input =
      ⟨r, k, a, b, false, i.val, x.val, y.val⟩ := by
  unfold inputStrand
  split_ifs <;> dsimp only [PushPuzzle.NCL.Word.DrawingData.LayerQuery.ofStrand, PushPuzzle.NCL.Word.DrawingData.LayerQuery.input, inputIndex] <;>
    simp only [Option.isNone_some] <;> congr 1 <;> omega

/-- The actual raw incoming-strand query equals the original full canonical layout trace. -/
theorem LayerInput.test_inputStrand {width k a b r : ℕ} (ha : k + a + r ≤ width)
    (hb : k + b + r ≤ width) (h3 : a + b = 3) (i : Fin (k + a + r))
    (x : Fin (Strip.Sweep.drawingWidth width + 1)) (y : Fin (4 * width + 7)) :
    PushPuzzle.NCL.Word.DrawingData.LayerInput.test width ⟨r, k, a, b, false, i.val, x.val, y.val⟩ =
      decide ((layer k a b r h3).Trace (inputStrand i) (x.val, y.val)) := by
  rw [← input_inputStrand ha hb h3 i x y, PushPuzzle.NCL.Word.DrawingData.LayerQuery.test_input, PushPuzzle.NCL.Word.DrawingData.LayerQuery.test_ofStrand]

/-- The actual raw created-output query equals the original full canonical layout trace. -/
theorem LayerInput.test_created {width k a b r : ℕ} (ha : k + a + r ≤ width)
    (hb : k + b + r ≤ width) (h3 : a + b = 3) (j : Fin b)
    (x : Fin (Strip.Sweep.drawingWidth width + 1)) (y : Fin (4 * width + 7)) :
    PushPuzzle.NCL.Word.DrawingData.LayerInput.test width ⟨r, k, a, b, true, j.val, x.val, y.val⟩ =
      decide ((layer k a b r h3).Trace (.inr (.inl (.inr j))) (x.val, y.val)) := by
  change (PushPuzzle.NCL.Word.DrawingData.LayerQuery.ofStrand ha hb h3 (.inr (.inl (.inr j))) x y).input.test width = _
  rw [PushPuzzle.NCL.Word.DrawingData.LayerQuery.test_input, PushPuzzle.NCL.Word.DrawingData.LayerQuery.test_ofStrand]

end PushPuzzle.NCL.Word.DrawingData
