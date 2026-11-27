/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.CompilePolyTime
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.TypingPolyTime
public import PushS.Source.Strip.Sweep.CanonicalDrawing
public import CslibFrontier.Computability.Geometry.Orthogonal.PointPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Standard encoded metadata of the actual canonical word drawing

Read the existing compiler's wire stack before each original layer. Its two boundary widths
give the exact height of the canonical two-band layout; prefix sums place the original vertices
in their original compilation order.

## Main definitions

* `PushPuzzle.NCL.Word.DrawingData.before`: actual original prefix compiler state.
* `PushPuzzle.NCL.Word.DrawingData.vertices`: canonical vertex positions in original layer order.

## Main results

* `PushPuzzle.NCL.Word.DrawingData.computableInPolyTime_vertices`: standard encoded coordinate emission.
-/

public section

namespace PushPuzzle.NCL.Word.DrawingData

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Word Cslib _root_.Turing.MultiTapeTM

private instance : ListEncoding encSlice encWord := by unfold encWord; infer_instance
private instance : SizedListEncoding encSlice encWord := by unfold encWord; infer_instance

/-- A structural primitive word paired with a unary original layer index. -/
abbrev encQuery := encPair encWord encUnary

/-- The exact original compiler state before the specified original layer. -/
@[expose] def before (w : Word) (i : ℕ) : Word.State := Word.run (w.take i) ⟨[], 0, []⟩

/-- The exact height from the original incoming and outgoing wire-stack widths. -/
@[expose] def heightAt (w : Word) (i : ℕ) : ℕ :=
  2 * (before w i).wires.length + 2 * (before w (i + 1)).wires.length + 6

/-- The original layer heights in chronological order. -/
@[expose] def heights (w : Word) : List ℕ := (List.range w.length).map (heightAt w)

/-- The first row of an original layer in the complete canonical drawing. -/
@[expose] def rowOffset (w : Word) (i : ℕ) : ℕ := (heights w |>.take i).sum

/-- Unary nonnegative horizontal/vertical coordinate pair. -/
abbrev encGridPoint : GridRouting.Point ↪ List Bool := encPair encUnary encUnary

/-- The actual canonical center on the original nonnegative grid. -/
@[expose] def gridPositionAt (w : Word) (i : ℕ) : GridRouting.Point :=
  let sl := (w.getD i (.swap 0)).data
  (4 * sl.offset + GridStar.center sl.inputs.length,
    rowOffset w i + 2 * ((before w i).wires.length + 1) + 1)

/-- The canonical center of the original layer in the standard integer coordinate plane. -/
@[expose] def positionAt (w : Word) (i : ℕ) : Orthogonal.Point :=
  ((gridPositionAt w i).1, (gridPositionAt w i).2)

/-- The original native vertex positions, in their original layer/compilation order. -/
@[expose] def vertices (w : Word) : Orthogonal.Route :=
  (List.range w.length).map (positionAt w)

/-- Reading an actual original prefix compiler state is standard polynomial-time. -/
theorem computableInPolyTime_before :
    ComputableInPolyTime (fun p : Word × ℕ => before p.1 p.2) encQuery Word.encState := by
  have ht : ComputableInPolyTime (fun p : Word × ℕ => p.1.take p.2) encQuery encWord := by
    exact ComputableInPolyTime.listTakeWithInput (ComputableInPolyTime.fst _ _)
      (ComputableInPolyTime.snd _ _)
  exact Word.computableInPolyTime_run_empty.comp ht

/-- The same two original boundary widths give a polynomial-time actual layer height. -/
private theorem computableInPolyTime_heightAt :
    ComputableInPolyTime (fun p : Word × ℕ => heightAt p.1 p.2) encQuery encUnary := by
  have hb := Word.State.computableInPolyTime_wires.comp computableInPolyTime_before
  have hi : ComputableInPolyTime (fun p : Word × ℕ => (p.1, p.2 + 1))
      encQuery encQuery := by unfold encQuery; fun_prop
  have ha := Word.State.computableInPolyTime_wires.comp (computableInPolyTime_before.comp hi)
  unfold heightAt
  fun_prop

/-- The actual complete chronological height list emits in standard polynomial time. -/
private theorem computableInPolyTime_heights :
    ComputableInPolyTime heights encWord (encList encUnary) := by
  unfold heights
  apply ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp
    (ComputableInPolyTime.length encSlice (encL := encWord)))
  exact computableInPolyTime_heightAt

/-- The exact original row offset is standard polynomial-time. -/
theorem computableInPolyTime_rowOffset :
    ComputableInPolyTime (fun p : Word × ℕ => rowOffset p.1 p.2) encQuery encUnary := by
  have hh := computableInPolyTime_heights.comp (ComputableInPolyTime.fst encWord encUnary)
  have hs : ComputableInPolyTime (fun ns : List ℕ => ns.sum) (encList encUnary) encUnary := by
    have hf : ComputableInPolyTime (fun ns : List ℕ => ns.flatMap fun n => List.replicate n false)
        (encList encUnary) (encList encBool) := by
      apply ComputableInPolyTime.flatMapWithInput ComputableInPolyTime.id'
      fun_prop
    have hl := (ComputableInPolyTime.length_list encBool).comp hf
    exact hl.of_enc_eq (fun ns => by simp)
  unfold rowOffset
  fun_prop

private theorem computableInPolyTime_center :
    ComputableInPolyTime GridStar.center encUnary encUnary := by
  unfold GridStar.center
  fun_prop

private theorem computableInPolyTime_layerData :
    ComputableInPolyTime (fun p : Word × ℕ => (p.1.getD p.2 (.swap 0)).data)
      encQuery Slice.encData :=
  Slice.computableInPolyTime_data.comp
    (ComputableInPolyTime.listGetDWithInput (ComputableInPolyTime.fst encWord encUnary)
      (ComputableInPolyTime.snd encWord encUnary) (.swap 0))

private theorem computableInPolyTime_column :
    ComputableInPolyTime (fun p : Word × ℕ =>
      4 * (p.1.getD p.2 (.swap 0)).data.offset +
        GridStar.center (p.1.getD p.2 (.swap 0)).data.inputs.length) encQuery encUnary := by
  have hk := Slice.encData_offset_polyTime computableInPolyTime_layerData
  have hc := computableInPolyTime_center.comp
    (ComputableInPolyTime.length encColor |>.comp
      (Slice.encData_inputs_polyTime computableInPolyTime_layerData))
  fun_prop

private theorem computableInPolyTime_row :
    ComputableInPolyTime (fun p : Word × ℕ =>
      rowOffset p.1 p.2 + 2 * ((before p.1 p.2).wires.length + 1) + 1) encQuery encUnary := by
  have hw := Word.State.computableInPolyTime_wires.comp computableInPolyTime_before
  have hr := computableInPolyTime_rowOffset
  fun_prop

/-- The same actual original grid center emits in standard unary nonnegative coordinates. -/
theorem computableInPolyTime_gridPositionAt :
    ComputableInPolyTime (fun p : Word × ℕ => gridPositionAt p.1 p.2)
      encQuery encGridPoint :=
  (computableInPolyTime_column.prod computableInPolyTime_row).of_enc_eq (fun _ => rfl)

/-- Emit the actual canonical center of one original layer in standard binary coordinates. -/
private theorem computableInPolyTime_positionAt :
    ComputableInPolyTime (fun p : Word × ℕ => positionAt p.1 p.2)
      encQuery Orthogonal.encPoint := by
  have hn := computableInPolyTime_gridPositionAt
  have hnz := ComputableInPolyTime.intBin_natCast.comp ComputableInPolyTime.unary_to_binary
  have hz : ComputableInPolyTime (fun p : ℕ × ℕ => ((p.1 : ℤ), (p.2 : ℤ)))
      (encPair encUnary encUnary) Orthogonal.encPoint :=
    (hnz.comp (ComputableInPolyTime.fst _ _)).prod
      (hnz.comp (ComputableInPolyTime.snd _ _))
  exact (hz.comp hn).of_enc_eq (fun _ => rfl)

/-- Original canonical vertex positions emit in standard encoded polynomial time. -/
theorem computableInPolyTime_vertices :
    ComputableInPolyTime vertices encWord Orthogonal.encRoute := by
  unfold vertices
  apply ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp
    (ComputableInPolyTime.length encSlice (encL := encWord)))
  exact computableInPolyTime_positionAt

end PushPuzzle.NCL.Word.DrawingData
