/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramPolyTimeEmitter
public import PushS.SegmentRecipePolyTime
import all PushS.SegmentRecipePolyTime
import Mathlib.Data.List.Nodup

/-! The actual finite target-hole bitmap as an explicitly computed duplicate-free unary point list. -/

public section
namespace PushPuzzle.PushS.SegmentRecipe

open Turing.MultiTapeTM

/-- Query the actual represented segment union with its existing standard machine. -/
@[fun_prop] theorem holeTest_polyTime : ComputableInPolyTime holeTest encHoleQuery encBool :=
  computableInPolyTime_holeTest

end PushPuzzle.PushS.SegmentRecipe

namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS Turing.MultiTapeTM

/-- A literal unary rectangle and its actual target segments. -/
structure PointSource where
  width : ℕ
  height : ℕ
  segments : List Segment

/-- The actual target-point source uses the existing unary dimensions and segment codec. -/
enc_structure encPointSource : PointSource where
  width : encUnary, height : encUnary, segments : (encList encSegment)

/-- All actual rectangle points, in increasing column-major order. -/
@[expose] def rectanglePoints (w h : ℕ) : List (ℕ × ℕ) := (List.range w).product (List.range h)

/-- The actual represented target holes, restricted to the declared finite rectangle. -/
@[expose] def holePoints (source : PointSource) : List (ℕ × ℕ) :=
  (rectanglePoints source.width source.height).filter fun point => SegmentRecipe.holeTest (source.segments, point)

/-- Literal cells retain exactly their natural coordinate pair. -/
@[expose] def cellPoint (w h : ℕ) : Cell w h ↪ ℕ × ℕ where
  toFun q := (q.1.val, q.2.val)
  inj' := by
    intro a b he
    exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

/-- Rectangle membership is exactly the two actual coordinate bounds. -/
theorem mem_rectanglePoints (w h : ℕ) (point : ℕ × ℕ) :
    point ∈ rectanglePoints w h ↔ point.1 < w ∧ point.2 < h := by
  rcases point with ⟨x, y⟩
  exact (List.mem_product (l₁ := List.range w) (l₂ := List.range h)).trans
    (by simp only [List.mem_range])

/-- Each actual rectangle point is enumerated once. -/
theorem rectanglePoints_nodup (w h : ℕ) : (rectanglePoints w h).Nodup :=
  List.nodup_range.product List.nodup_range

/-- Each actual target-hole point is enumerated once. -/
theorem holePoints_nodup (source : PointSource) : (holePoints source).Nodup :=
  (rectanglePoints_nodup source.width source.height).filter _

/-- The explicit rectangle enumeration has an actual standard polynomial-time machine. -/
@[fun_prop] theorem rectanglePoints_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ => rectanglePoints p.1 p.2) Bitmap.encPoint (encList Bitmap.encPoint) := by
  have hrow : ComputableInPolyTime (fun p : ℕ × ℕ => (List.range p.1).map fun y => (p.2, y))
      Bitmap.encPoint (encList Bitmap.encPoint) := by
    have hc : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => (p.1.2, p.2))
        (encPair Bitmap.encPoint encUnary) Bitmap.encPoint := by unfold Bitmap.encPoint; fun_prop
    exact ComputableInPolyTime.mapWithInput (f := fun (p : ℕ × ℕ) (y : ℕ) => (p.2, y)) (by unfold Bitmap.encPoint; fun_prop) hc
  have hargs : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => (p.1.2, p.2))
      (encPair Bitmap.encPoint encUnary) Bitmap.encPoint := by unfold Bitmap.encPoint; fun_prop
  have hcallback : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => (List.range p.1.2).map fun y => (p.2, y))
      (encPair Bitmap.encPoint encUnary) (encList Bitmap.encPoint) := hrow.comp hargs
  unfold rectanglePoints List.product
  exact ComputableInPolyTime.flatMapWithInput (f := fun (p : ℕ × ℕ) x => (List.range p.2).map fun y => (x, y))
    (by unfold Bitmap.encPoint; fun_prop) hcallback

/-- Every actual target-hole point emits from the original rectangle and segment list in standard polynomial time. -/
@[fun_prop] theorem holePoints_polyTime : ComputableInPolyTime holePoints encPointSource (encList Bitmap.encPoint) := by
  have hdim : ComputableInPolyTime (fun source : PointSource => (source.width, source.height))
      encPointSource Bitmap.encPoint := by unfold Bitmap.encPoint; fun_prop
  have hr : ComputableInPolyTime (fun source : PointSource => rectanglePoints source.width source.height)
      encPointSource (encList Bitmap.encPoint) := rectanglePoints_polyTime.comp hdim
  have hargs : ComputableInPolyTime (fun p : PointSource × (ℕ × ℕ) => (p.1.segments, p.2))
      (encPair encPointSource Bitmap.encPoint) SegmentRecipe.encHoleQuery := by unfold SegmentRecipe.encHoleQuery; fun_prop
  have ht := SegmentRecipe.holeTest_polyTime.comp hargs
  unfold holePoints
  exact ComputableInPolyTime.filterWithInput (test := fun (source : PointSource) point => SegmentRecipe.holeTest (source.segments, point)) hr ht

/-- The computed point list is exactly the actual finite target-hole set under its literal coordinate embedding. -/
theorem holePoints_finset (source : PointSource) :
    (holePoints source).toFinset =
      (SegmentRecipe.holes source.width source.height source.segments).map (cellPoint source.width source.height) := by
  ext point
  rcases point with ⟨x, y⟩
  simp only [holePoints, List.mem_toFinset, List.mem_filter, mem_rectanglePoints, Finset.mem_map]
  constructor
  · rintro ⟨⟨hx, hy⟩, hh⟩
    refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩
  · rintro ⟨q, hq, he⟩
    have hx : q.1.val = x := congrArg Prod.fst he
    have hy : q.2.val = y := congrArg Prod.snd he
    rw [← hx, ← hy]
    exact ⟨⟨q.1.isLt, q.2.isLt⟩, (Finset.mem_filter.mp hq).2⟩

/-- Filtering a genuine point enumeration counts exactly the corresponding finite-cell filter. -/
theorem point_filter_count {w h : ℕ} (points : List (ℕ × ℕ)) (E : Finset (Cell w h))
    (hn : points.Nodup) (he : points.toFinset = E.map (cellPoint w h)) (keep : (ℕ × ℕ) → Bool) :
    (points.filter keep).length = (E.filter fun q => keep (cellPoint w h q)).card := by
  have hf : (points.filter keep).toFinset = points.toFinset.filter (fun p => keep p) := by
    ext p
    simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter]
  calc
    (points.filter keep).length = ((points.filter keep).toFinset).card := (List.toFinset_card_of_nodup (hn.filter keep)).symm
    _ = (E.filter fun q => keep (cellPoint w h q)).card := by
      rw [hf, he, Finset.filter_map, Finset.card_map]
      simp only [Function.comp_def]

end PushPuzzle.Push.AcceptanceProgram
