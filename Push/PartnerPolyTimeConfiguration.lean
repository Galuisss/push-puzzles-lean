/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerPolyTimeCuts
public import Push.PartnerConfigurationRepair

/-! Total physical direction-word emission for the actual ear and common-cut programs. -/

public section
namespace PushPuzzle.Push.Partner

open PushS Turing.MultiTapeTM
open scoped PushPuzzle.PushS PushPuzzle.Push.Partner

/-- The existing framed Boolean-list encoding of actual physical-axis words. -/
abbrev encAxes : List Bool ↪ List Bool := encList encBool

/-- The actual evolving layout/position table and its complete physical-axis word. -/
abbrev encScanState : (BufferState × List Bool) ↪ List Bool := encPair encBufferState encAxes

@[fun_prop] theorem earState_polyTime : ComputableInPolyTime
    (fun p : PortLayout × ℕ × List Bool × Bool × Bool => earState p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    (encPair encPortLayout (encPair encUnary (encPair encAxes (encPair encBool encBool)))) encAxes := by
  unfold earState earValue unshift encAxes
  fun_prop

/-- Emit every original and fresh axis direction of the literal ear on all raw inputs. -/
@[fun_prop] theorem earExtend_polyTime : ComputableInPolyTime
    (fun p : PortLayout × ℕ × (ℕ × ℕ) × List Bool => earExtend p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair encPortLayout (encPair encUnary (encPair encPortPair encAxes))) encAxes := by
  unfold earExtend
  fun_prop

@[fun_prop] theorem earRestrict_polyTime : ComputableInPolyTime
    (fun p : PortLayout × ℕ × List Bool => earRestrict p.1 p.2.1 p.2.2)
    (encPair encPortLayout (encPair encUnary encAxes)) encAxes := by
  unfold earRestrict encAxes
  fun_prop

@[fun_prop] theorem bufferAtAxes_polyTime : ComputableInPolyTime
    (fun p : BufferState × ℕ × List Bool => bufferAtAxes p.1 p.2.1 p.2.2)
    (encPair encBufferState (encPair encUnary encAxes)) encAxes := by
  unfold bufferAtAxes
  fun_prop

namespace BufferState

/-- Run the same actual gate inspection on both the layout and its direction array. -/
def scanStep (s : BufferState × List Bool) (first : ℕ) : BufferState × List Bool :=
  (s.1.bufferAt first, bufferAtAxes s.1 first s.2)

@[fun_prop] theorem scanStep_polyTime : ComputableInPolyTime
    (fun p : (BufferState × List Bool) × ℕ => scanStep p.1 p.2)
    (encPair encScanState encUnary) encScanState := by
  unfold scanStep encScanState
  fun_prop

theorem scanStep_fold (s : BufferState) (positions : List ℕ) (axes : List Bool) :
    positions.foldl scanStep (s, axes) = (s.scan positions, Partner.scanAxes s positions axes) := by
  induction positions generalizing s axes with
  | nil => rfl
  | cons first rest ih => exact ih (s.bufferAt first) (bufferAtAxes s first axes)

end BufferState
namespace Cuts

private abbrev CutQuery := PortLayout × ℕ × List Bool × List Bool × List Bool × ℕ
private abbrev encCutQuery : CutQuery ↪ List Bool :=
  encPair encPortLayout (encPair encUnary (encPair encAxes (encPair encAxes (encPair encAxes encUnary))))

@[fun_prop] private theorem cutValue_polyTime : ComputableInPolyTime
    (fun p : CutQuery =>
      cutValue p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
    encCutQuery encBool := by
  have hc : ComputableInPolyTime (fun p : CutQuery => (active p.1 p.2.1).length)
      encCutQuery encUnary := by unfold encCutQuery; fun_prop
  have hi : ComputableInPolyTime (fun p : CutQuery => p.2.2.2.2.2) encCutQuery encUnary := by
    unfold encCutQuery
    fun_prop
  have hk : ComputableInPolyTime (fun p : CutQuery => p.2.1) encCutQuery encUnary := by
    unfold encCutQuery
    fun_prop
  have ha : ComputableInPolyTime (fun p : CutQuery => p.2.2.1) encCutQuery encAxes := by
    unfold encCutQuery
    fun_prop
  have hl : ComputableInPolyTime (fun p : CutQuery => p.2.2.2.1) encCutQuery encAxes := by
    unfold encCutQuery
    fun_prop
  have hr : ComputableInPolyTime (fun p : CutQuery => p.2.2.2.2.1) encCutQuery encAxes := by
    unfold encCutQuery
    fun_prop
  unfold cutValue
  dsimp only
  fun_prop

@[fun_prop] theorem cutState_polyTime : ComputableInPolyTime
    (fun p : PortLayout × ℕ × List Bool × List Bool × List Bool =>
      cutState p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    (encPair encPortLayout (encPair encUnary (encPair encAxes (encPair encAxes encAxes)))) encAxes := by
  unfold cutState
  fun_prop

@[fun_prop] theorem activeValues_polyTime : ComputableInPolyTime
    (fun p : PortLayout × ℕ × List Bool × Bool => activeValues p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair encPortLayout (encPair encUnary (encPair encAxes encBool))) encAxes := by
  unfold activeValues encAxes
  fun_prop

/-- The entire common-cut axis word is emitted in polynomial time on arbitrary raw layouts. -/
@[fun_prop] theorem cutExtend_polyTime : ComputableInPolyTime
    (fun p : PortLayout × ℕ × List Bool => cutExtend p.1 p.2.1 p.2.2)
    (encPair encPortLayout (encPair encUnary encAxes)) encAxes := by
  unfold cutExtend
  fun_prop

@[fun_prop] theorem cutRestrict_polyTime : ComputableInPolyTime
    (fun p : PortLayout × ℕ × List Bool => cutRestrict p.1 p.2.1 p.2.2)
    (encPair encPortLayout (encPair encUnary encAxes)) encAxes := by
  unfold cutRestrict encAxes
  fun_prop

@[fun_prop] theorem cutAtAxes_polyTime : ComputableInPolyTime
    (fun p : BufferState × ℕ × List Bool => cutAtAxes p.1 p.2.1 p.2.2)
    (encPair encBufferState (encPair encUnary encAxes)) encAxes := by
  unfold cutAtAxes
  fun_prop

/-- Run the same actual safe-cut decision on the layout and its complete direction word. -/
def scanStep (s : BufferState × List Bool) (cut : ℕ) : BufferState × List Bool :=
  (cutAt s.1 cut, cutAtAxes s.1 cut s.2)

@[fun_prop] theorem scanStep_polyTime : ComputableInPolyTime
    (fun p : (BufferState × List Bool) × ℕ => scanStep p.1 p.2)
    (encPair encScanState encUnary) encScanState := by
  unfold scanStep encScanState
  fun_prop

theorem scanStep_fold (s : BufferState) (positions : List ℕ) (axes : List Bool) :
    positions.foldl scanStep (s, axes) = (scan s positions, scanAxes s positions axes) := by
  induction positions generalizing s axes with
  | nil => rfl
  | cons cut rest ih => exact ih (cutAt s cut) (cutAtAxes s cut axes)

end Cuts
end PushPuzzle.Push.Partner
