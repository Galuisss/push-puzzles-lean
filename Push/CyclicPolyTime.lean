/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Cyclic
public import Push.ColumnScanPolyTime
public import Push.CornerDockPolyTime

/-! Standard polynomial-time construction of one widened cyclic reader stage. -/

public section
namespace PushPuzzle.Push.Cyclic

open Turing.MultiTapeTM
open scoped PushPuzzle.Push.ColumnScan

private theorem width_polyTime : ComputableInPolyTime ColumnScan.Input.width
    ColumnScan.Input.encoding encUnary :=
  ColumnScan.encData_width_polyTime ColumnScan.Input.data_polyTime

private theorem height_polyTime : ComputableInPolyTime ColumnScan.Input.height
    ColumnScan.Input.encoding encUnary :=
  ColumnScan.encData_height_polyTime ColumnScan.Input.data_polyTime

/-- Set the east room's width directly in the serialized source recipe. -/
@[fun_prop] theorem wideReader_polyTime : ComputableInPolyTime wideReader
    ColumnScan.Input.encoding ColumnScan.Input.encoding := by
  have hw := width_polyTime
  have he : ComputableInPolyTime ColumnScan.Input.extraWidth ColumnScan.Input.encoding encUnary :=
    ColumnScan.encData_extraWidth_polyTime ColumnScan.Input.data_polyTime
  have h : ComputableInPolyTime
      (fun r : ColumnScan.Input => { ColumnScan.Input.data r with extraWidth := r.width + 1 + r.extraWidth })
      ColumnScan.Input.encoding ColumnScan.encData := by
    fun_prop
  exact h.of_enc_eq fun _ => rfl

/-- The dock's serialized source is precisely the already emitted widened reader. -/
@[fun_prop] theorem dock_polyTime : ComputableInPolyTime dock
    ColumnScan.Input.encoding CornerDock.Input.encoding :=
  (ColumnScan.Input.compile_polyTime.comp wideReader_polyTime).of_enc_eq
    (fun r => congrArg Push.encoding (dock_source r))

/-- The quarter turn writes the actual dense game in polynomial time. -/
@[fun_prop] theorem turn_polyTime : ComputableInPolyTime turn Push.encoding Push.encoding :=
  Push.Instance.transposed_polyTime.comp Push.Instance.reflectedX_polyTime

/-- The complete next live source is a standard polynomial-time output. -/
@[fun_prop] theorem nextSource_polyTime : ComputableInPolyTime nextSource
    ColumnScan.Input.encoding Push.encoding :=
  turn_polyTime.comp (CornerDock.Input.compile_polyTime.comp dock_polyTime)

private theorem readerHeight_polyTime : ComputableInPolyTime
    (fun r => (wideReader r).outputHeight) ColumnScan.Input.encoding encUnary :=
  (ColumnScan.Data.outputHeight_polyTime.comp
    (ColumnScan.Input.data_polyTime.comp wideReader_polyTime)).of_enc_eq
      (fun r => congrArg encUnary (ColumnScan.Input.data_outputHeight (wideReader r)).symm)

private theorem readerTarget_polyTime : ComputableInPolyTime
    (fun r => (wideReader r).targetLevel) ColumnScan.Input.encoding encUnary :=
  (ColumnScan.Data.targetLevel_polyTime.comp
    (ColumnScan.Input.data_polyTime.comp wideReader_polyTime)).of_enc_eq
      (fun r => congrArg encUnary (ColumnScan.Input.data_targetLevel (wideReader r)).symm)

private theorem dockHeight_polyTime : ComputableInPolyTime
    (fun r => (dock r).outputHeight) ColumnScan.Input.encoding encUnary := by
  have hh := readerHeight_polyTime
  have ht := readerTarget_polyTime
  change ComputableInPolyTime (fun r => (wideReader r).outputHeight +
    ((wideReader r).outputHeight - (wideReader r).targetLevel)) ColumnScan.Input.encoding encUnary
  fun_prop

/-- Source-row quotas, auxiliary-row clear quotas, and final zero padding are emitted explicitly. -/
@[fun_prop] theorem nextQuotas_polyTime : ComputableInPolyTime
    (fun q : ColumnScan.Input × List ℕ => nextQuotas q.1 q.2)
    (encPair ColumnScan.Input.encoding (encList encUnary)) (encList encUnary) := by
  have hw := width_polyTime
  have hh := height_polyTime
  have hreader := readerHeight_polyTime
  have hdock := dockHeight_polyTime
  have hreaderQ : ComputableInPolyTime
      (fun q : ColumnScan.Input × List ℕ => (wideReader q.1).outputHeight)
      (encPair ColumnScan.Input.encoding (encList encUnary)) encUnary :=
    readerHeight_polyTime.comp (ComputableInPolyTime.fst _ _)
  have hdockQ : ComputableInPolyTime
      (fun q : ColumnScan.Input × List ℕ => (dock q.1).outputHeight)
      (encPair ColumnScan.Input.encoding (encList encUnary)) encUnary :=
    dockHeight_polyTime.comp (ComputableInPolyTime.fst _ _)
  have hz : ComputableInPolyTime
      (fun q : ColumnScan.Input × List ℕ =>
        List.replicate ((dock q.1).outputHeight - (wideReader q.1).outputHeight) (0 : ℕ))
      (encPair ColumnScan.Input.encoding (encList encUnary)) (encList encUnary) := by
    apply ComputableInPolyTime.replicate
    · fun_prop
    · exact ComputableInPolyTime.const 0
  unfold nextQuotas
  fun_prop

end PushPuzzle.Push.Cyclic
