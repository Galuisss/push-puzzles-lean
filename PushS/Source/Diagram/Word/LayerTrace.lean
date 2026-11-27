/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Diagram.Word.DrawingData
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Strand
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-!
# Actual bounded canonical layer-trace queries

The local input is a bounded original layer's exact shape, a strand slot and a local grid point.
The query evaluates the existing `GridLayout.layer` trace, including its two routing bands and
the actual three-port middle star. The bounded finite table uses standard field encodings.

## Main definitions

* `PushPuzzle.NCL.Word.DrawingData.LayerQuery`: the actual bounded local layout and query coordinates.
* `PushPuzzle.NCL.Word.DrawingData.LayerQuery.test`: query the existing full canonical strand trace.

## Main results

* `PushPuzzle.NCL.Word.DrawingData.LayerQuery.computableInPolyTime_test`: standard finite local trace query.
-/

public section

namespace PushPuzzle.NCL.Word.DrawingData

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Word Cslib _root_.Turing.MultiTapeTM GridLayout GridRouting

/-- An original bounded layer's actual shape, strand slot and local grid point. -/
structure LayerQuery (width : ℕ) where
  /-- Number of original unchanged suffix wires. -/
  suffix : Fin (width + 1)
  /-- Original cell offset in that live stack. -/
  offset : Fin (width + 1)
  /-- Number of original cell inputs. -/
  inputs : Fin 4
  /-- Number of original cell outputs. -/
  outputs : Fin 4
  /-- Select a newly created output strand rather than an original incoming strand. -/
  created : Bool
  /-- Original incoming-stack index or original cell-output index. -/
  slot : Fin (width + 1)
  /-- Original local query column. -/
  x : Fin (Strip.Sweep.drawingWidth width + 1)
  /-- Original local query row within the two-band layer. -/
  y : Fin (4 * width + 7)

/-- Canonical finite field encodings of the bounded original layout and local grid query. -/
enc_structure encLayerQuery (width : ℕ) : LayerQuery width where
  suffix : (encFinEnum (Fin (width + 1))), offset : (encFinEnum (Fin (width + 1))),
  inputs : (encFinEnum (Fin 4)), outputs : (encFinEnum (Fin 4)), created : encBool,
  slot : (encFinEnum (Fin (width + 1))),
  x : (encFinEnum (Fin (Strip.Sweep.drawingWidth width + 1))),
  y : (encFinEnum (Fin (4 * width + 7)))

private instance (width : ℕ) : Finite (LayerQuery width) :=
  Finite.of_injective
    (fun q : LayerQuery width =>
      (q.suffix, q.offset, q.inputs, q.outputs, q.created, q.slot, q.x, q.y))
    (by rintro ⟨_, _, _, _, _, _, _, _⟩ ⟨_, _, _, _, _, _, _, _⟩ h; cases h; rfl)

/-- The existing full layer trace is decidable by its finite band tests. -/
instance instDecidableTrace {k a b r : ℕ} (L : Layer k a b r)
    (e : Strand k a b r) (p : GridRouting.Point) : Decidable (L.Trace e p) := by
  unfold Layer.Trace GridDrawing.Shift OrderedRouting.Contains Elbow.Contains
  rcases e with i | ((i | j) | j) <;>
    dsimp only [MiddleContains, GridStar.Contains] <;> infer_instance

/-- Query the same actual canonical input/output strand of the original local grid layout. -/
@[expose] def LayerQuery.test {width : ℕ} (q : LayerQuery width) : Bool :=
  if h : q.inputs.val + q.outputs.val = 3 then
    let L := layer q.offset.val q.inputs.val q.outputs.val q.suffix.val h
    if q.created then
      if hj : q.slot.val < q.outputs.val then
        decide (L.Trace (.inr (.inl (.inr ⟨q.slot.val, hj⟩))) (q.x.val, q.y.val))
      else false
    else if hi : q.slot.val < q.offset.val + q.inputs.val + q.suffix.val then
      decide (L.Trace (inputStrand ⟨q.slot.val, by omega⟩) (q.x.val, q.y.val))
    else false
  else false

/-- Each bounded original canonical layer-trace query is standard encoded polynomial-time. -/
theorem LayerQuery.computableInPolyTime_test (width : ℕ) :
    ComputableInPolyTime (PushPuzzle.NCL.Word.DrawingData.LayerQuery.test (width := width)) (encLayerQuery width) encBool :=
  ComputableInPolyTime.of_finite _

/-- Retain an original canonical layer strand in the bounded finite query representation. -/
@[expose] def LayerQuery.ofStrand {width k a b r : ℕ} (ha : k + a + r ≤ width)
    (hb : k + b + r ≤ width) (h3 : a + b = 3) (e : Strand k a b r)
    (x : Fin (Strip.Sweep.drawingWidth width + 1)) (y : Fin (4 * width + 7)) :
    LayerQuery width where
  suffix := ⟨r, by omega⟩
  offset := ⟨k, by omega⟩
  inputs := ⟨a, by omega⟩
  outputs := ⟨b, by omega⟩
  created := (inputIndex e).isNone
  slot := match e with
    | .inl i => ⟨i.val, by have := i.isLt; omega⟩
    | .inr (.inl (.inl i)) => ⟨k + i.val, by have := i.isLt; omega⟩
    | .inr (.inl (.inr j)) => ⟨j.val, by have := j.isLt; omega⟩
    | .inr (.inr j) => ⟨k + a + j.val, by have := j.isLt; omega⟩
  x := x
  y := y

/-- The finite query evaluates precisely the same original full canonical strand trace. -/
theorem LayerQuery.test_ofStrand {width k a b r : ℕ} (ha : k + a + r ≤ width)
    (hb : k + b + r ≤ width) (h3 : a + b = 3) (e : Strand k a b r)
    (x : Fin (Strip.Sweep.drawingWidth width + 1)) (y : Fin (4 * width + 7)) :
    (PushPuzzle.NCL.Word.DrawingData.LayerQuery.ofStrand ha hb h3 e x y).test =
      decide ((layer k a b r h3).Trace e (x.val, y.val)) := by
  rcases e with i | ((i | j) | j)
  all_goals dsimp only [PushPuzzle.NCL.Word.DrawingData.LayerQuery.ofStrand, PushPuzzle.NCL.Word.DrawingData.LayerQuery.test, inputIndex]
  all_goals simp (disch := omega) [h3,
      inputStrand, show ∀ n < k, n < k + a + r by omega,
      show ∀ n < a, k + n < k + a + r by omega,
      show ∀ n, ¬k + a + n < k by omega]

end PushPuzzle.NCL.Word.DrawingData
