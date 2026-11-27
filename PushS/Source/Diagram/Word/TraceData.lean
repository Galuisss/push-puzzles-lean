/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Diagram.Word.LayerInput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Standard encoded queries of the original canonical word traces

The original compiler prefix gives each live wire's native edge label and the next created
edge label. Query those exact strands in the original layer's canonical layout, translated by
its actual row offset. The complete query scans the original layers in order.

## Main definitions

* `PushPuzzle.NCL.Word.DrawingData.TraceInput`: original native word, native edge and grid point.
* `PushPuzzle.NCL.Word.DrawingData.TraceInput.trace`: scan the actual canonical strand traces.

## Main results

* `PushPuzzle.NCL.Word.DrawingData.TraceInput.computableInPolyTime_trace`: standard encoded trace queries.
-/

public section

namespace PushPuzzle.NCL.Word.DrawingData

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Word Cslib _root_.Turing.MultiTapeTM

/-- An original native edge at an original nonnegative grid point of the original word. -/
structure TraceInput where
  /-- The exact original structurally encoded primitive word. -/
  word : Word
  /-- The original native creation-order edge label. -/
  edge : ℕ
  /-- Original grid column. -/
  x : ℕ
  /-- Original grid row. -/
  y : ℕ

/-- Original structural word, unary native edge label, and unary nonnegative coordinates. -/
enc_structure encTraceInput : TraceInput where
  word : encWord, edge : encUnary, x : encUnary, y : encUnary

/-- The original layer index is unary and follows the framed original trace query. -/
abbrev encTraceLayer := encPair encTraceInput encUnary

/-- The original layer index is followed by the original source-side tag and unary strand slot.
-/
abbrev encTraceSlot := encPair encTraceLayer (encPair encBool encUnary)

/-- Original source/shape fields for one actual original layer strand at the queried point. -/
@[expose] def TraceInput.query (input : TraceInput) (i : ℕ) (created : Bool) (slot : ℕ) :
    LayerInput :=
  let sl := (input.word.getD i (.swap 0)).data
  let st := before input.word i
  { suffix := st.wires.length - (sl.offset + sl.inputs.length)
    offset := sl.offset
    inputs := sl.inputs.length
    outputs := sl.outputs.length
    created := created
    slot := slot
    x := input.x
    y := input.y - rowOffset input.word i }

/-- Check all original live and newly created native edge strands in one original layer. -/
@[expose] def TraceInput.atLayer (width : ℕ) (input : TraceInput) (i : ℕ) : Bool :=
  let st := before input.word i
  let sl := (input.word.getD i (.swap 0)).data
  if rowOffset input.word i ≤ input.y ∧ input.x ≤ Strip.Sweep.drawingWidth width ∧
      input.y - rowOffset input.word i ≤ 4 * width + 6 then
    ((List.range st.wires.length).any fun j =>
      (st.wires.getD j 0 == input.edge) && (input.query i false j).test width) ||
    ((List.range sl.outputs.length).any fun j =>
      (st.next + j == input.edge) && (input.query i true j).test width)
  else false

/-- The same original native edge's complete canonical trace, in the original scan order. -/
@[expose] def TraceInput.trace (width : ℕ) (input : TraceInput) : Bool :=
  (List.range input.word.length).any (input.atLayer width)

private theorem computableInPolyTime_before_trace :
    ComputableInPolyTime (fun p : TraceInput × ℕ => before p.1.word p.2)
      encTraceLayer Word.encState := by
  have hi : ComputableInPolyTime (fun p : TraceInput × ℕ => (p.1.word, p.2))
      encTraceLayer encQuery := by fun_prop
  exact (computableInPolyTime_before.comp hi).of_enc_eq (fun _ => rfl)

private theorem computableInPolyTime_slice_trace :
    ComputableInPolyTime (fun p : TraceInput × ℕ => (p.1.word.getD p.2 (.swap 0)).data)
      encTraceLayer Slice.encData := by
  apply Slice.computableInPolyTime_data.comp
  fun_prop

private theorem computableInPolyTime_offset_trace :
    ComputableInPolyTime (fun p : TraceInput × ℕ => rowOffset p.1.word p.2)
      encTraceLayer encUnary := by
  have hi : ComputableInPolyTime (fun p : TraceInput × ℕ => (p.1.word, p.2))
      encTraceLayer encQuery := by fun_prop
  exact (computableInPolyTime_rowOffset.comp hi).of_enc_eq (fun _ => rfl)

/-- Each original strand's actual source, shape and local coordinates emit in polynomial time. -/
private theorem TraceInput.computableInPolyTime_query :
    ComputableInPolyTime (fun p : (TraceInput × ℕ) × (Bool × ℕ) =>
      p.1.1.query p.1.2 p.2.1 p.2.2) encTraceSlot encLayerInput := by
  have hf := ComputableInPolyTime.fst encTraceLayer (encPair encBool encUnary)
  have hs := computableInPolyTime_slice_trace.comp hf
  have hw := Word.State.computableInPolyTime_wires.comp (computableInPolyTime_before_trace.comp hf)
  have ho := computableInPolyTime_offset_trace.comp hf
  unfold PushPuzzle.NCL.Word.DrawingData.TraceInput.query
  apply encLayerInput_mk_polyTime <;> fun_prop

/-- The original local strand query uses the same standard finite-table dispatcher. -/
private theorem TraceInput.computableInPolyTime_query_test (width : ℕ) :
    ComputableInPolyTime (fun p : (TraceInput × ℕ) × (Bool × ℕ) =>
      (p.1.1.query p.1.2 p.2.1 p.2.2).test width) encTraceSlot encBool :=
  ((PushPuzzle.NCL.Word.DrawingData.LayerInput.computableInPolyTime_test width).comp
    PushPuzzle.NCL.Word.DrawingData.TraceInput.computableInPolyTime_query).of_enc_eq (fun _ => rfl)

private theorem computableInPolyTime_test_slot (width : ℕ) (created : Bool) :
    ComputableInPolyTime (fun p : (TraceInput × ℕ) × ℕ =>
      (p.1.1.query p.1.2 created p.2).test width)
      (encPair encTraceLayer encUnary) encBool := by
  have hi : ComputableInPolyTime (fun p : (TraceInput × ℕ) × ℕ =>
      (p.1, (created, p.2))) (encPair encTraceLayer encUnary) encTraceSlot := by fun_prop
  exact ((PushPuzzle.NCL.Word.DrawingData.TraceInput.computableInPolyTime_query_test width).comp hi).of_enc_eq (fun _ => rfl)

private theorem computableInPolyTime_incoming_scan (width : ℕ) :
    ComputableInPolyTime (fun p : TraceInput × ℕ =>
      (List.range (before p.1.word p.2).wires.length).any fun j =>
        ((before p.1.word p.2).wires.getD j 0 == p.1.edge) &&
          (p.1.query p.2 false j).test width) encTraceLayer encBool := by
  have hw := Word.State.computableInPolyTime_wires.comp computableInPolyTime_before_trace
  apply ComputableInPolyTime.anyWithInput (ComputableInPolyTime.range.comp
    ((ComputableInPolyTime.length_list encUnary).comp hw))
  have hww := hw.comp (ComputableInPolyTime.fst encTraceLayer encUnary)
  have ht := computableInPolyTime_test_slot width false
  fun_prop

private theorem computableInPolyTime_created_scan (width : ℕ) :
    ComputableInPolyTime (fun p : TraceInput × ℕ =>
      (List.range (p.1.word.getD p.2 (.swap 0)).data.outputs.length).any fun j =>
        ((before p.1.word p.2).next + j == p.1.edge) &&
          (p.1.query p.2 true j).test width) encTraceLayer encBool := by
  have hs := computableInPolyTime_slice_trace
  have hn := Word.State.computableInPolyTime_next.comp computableInPolyTime_before_trace
  apply ComputableInPolyTime.anyWithInput
    (ComputableInPolyTime.range.comp ((ComputableInPolyTime.length_list encColor).comp
      (Slice.encData_outputs_polyTime hs)))
  have hnn := hn.comp (ComputableInPolyTime.fst encTraceLayer encUnary)
  have ht := computableInPolyTime_test_slot width true
  fun_prop

/-- The complete original strand-label scan in one actual layer is standard polynomial-time. -/
private theorem TraceInput.computableInPolyTime_atLayer (width : ℕ) :
    ComputableInPolyTime (fun p : TraceInput × ℕ => p.1.atLayer width p.2)
      encTraceLayer encBool := by
  have hl := computableInPolyTime_incoming_scan width
  have hr := computableInPolyTime_created_scan width
  have ho := computableInPolyTime_offset_trace
  unfold PushPuzzle.NCL.Word.DrawingData.TraceInput.atLayer
  dsimp only
  fun_prop

/-- The complete original canonical trace query is standard encoded polynomial-time. -/
theorem TraceInput.computableInPolyTime_trace (width : ℕ) :
    ComputableInPolyTime (PushPuzzle.NCL.Word.DrawingData.TraceInput.trace width) encTraceInput encBool := by
  unfold PushPuzzle.NCL.Word.DrawingData.TraceInput.trace
  apply ComputableInPolyTime.anyWithInput
  · fun_prop
  · exact PushPuzzle.NCL.Word.DrawingData.TraceInput.computableInPolyTime_atLayer width

end PushPuzzle.NCL.Word.DrawingData
