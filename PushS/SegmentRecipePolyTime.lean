/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.SegmentRecipe

/-!
# Polynomial-time emission of wall-free hole-segment recipes

Dimensions and segment coordinates use the existing unary encodings. The emitter writes the
whole rectangle, querying the represented segment union at every cell. Validity concerns only
the player and equal storage inventories; the machine computes the same dense output on all
raw recipes.

## Main results

* `SegmentRecipe.computableInPolyTime_emit`: the actual dense recipe emitter is polynomial-time.
* `SegmentRecipe.computableInPolyTime_toInstance`: the genuine instance constructor has that
  same polynomial-time encoded output.
-/

public section

namespace PushPuzzle.PushS.SegmentRecipe


open PushFS PushFS.Reduction
open _root_.Turing.MultiTapeTM
open scoped PushFS.Encoding

private theorem computableInPolyTime_holeTest :
    ComputableInPolyTime holeTest encHoleQuery encBool := by
  have hc : ComputableInPolyTime (fun ss : List Segment => ss.flatMap Segment.cells)
      (encList encSegment) (encList Bitmap.encPoint) := by fun_prop
  have he : ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1 == p.2)
      (encPair Bitmap.encPoint Bitmap.encPoint) encBool :=
    ComputableInPolyTime.beq (ComputableInPolyTime.fst _ _) (ComputableInPolyTime.snd _ _)
  change ComputableInPolyTime
    (fun q : List Segment × ℕ × ℕ => (q.1.flatMap Segment.cells).contains q.2)
    (encPair (encList encSegment) Bitmap.encPoint) encBool
  simpa only [List.contains_eq_any_beq, Function.comp_def] using
    ComputableInPolyTime.anyWithEncoding he (ComputableInPolyTime.snd _ _)
      (hc.comp (ComputableInPolyTime.fst _ _))

@[local fun_prop] private theorem computableInPolyTime_tile :
    ComputableInPolyTime tile encQuery Encoding.encTile := by
  have hi : ComputableInPolyTime
      (fun p : SegmentRecipe × ℕ × ℕ => holeTest (p.1.initialSegments, p.2)) encQuery encBool :=
    computableInPolyTime_holeTest.comp (by unfold encQuery; fun_prop)
  have ht : ComputableInPolyTime
      (fun p : SegmentRecipe × ℕ × ℕ => holeTest (p.1.targetSegments, p.2)) encQuery encBool :=
    computableInPolyTime_holeTest.comp (by unfold encQuery; fun_prop)
  unfold tile encQuery Bitmap.encPoint
  fun_prop

/-- The full dense output is polynomial-time in the raw unary recipe encoding. -/
@[fun_prop]
theorem computableInPolyTime_emit :
    ComputableInPolyTime emit encSegmentRecipe Encoding.encData := by
  unfold emit
  fun_prop

/-- Constructing actual wall-free instances computes the emitted bitmap, with no proof data. -/
theorem computableInPolyTime_toInstance {α : Type} {enc : α ↪ List Bool}
    {recipe : α → SegmentRecipe} (hr : ComputableInPolyTime recipe enc encSegmentRecipe)
    (hv : ∀ a, (recipe a).Valid) :
    ComputableInPolyTime (fun a => (recipe a).toInstance (hv a)) enc encoding :=
  (computableInPolyTime_emit.comp hr).of_enc_eq
    (fun a => congrArg Encoding.encData ((recipe a).data_eq (hv a)))

end PushPuzzle.PushS.SegmentRecipe
