/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.WordSource
public import PushS.PortSegments
public import PushS.CombUpperActive

/-! Polynomial-time complete wall-free recipes for the actual fixed-alphabet source family. -/

public section
namespace PushPuzzle.PushS.WordSource

open Cslib.Complexity

open _root_.Turing.MultiTapeTM

/-- The explicit constant level budget of the original fixed-alphabet strip family. -/
@[expose] def levelBudget (q : ℕ) : ℕ :=
  2 * ((2 * PushPuzzle.NCL.HWord.Strip.Sweep.drawingSpan q + 1) *
    (4 * PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q + 7))

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- Allocate one spare axis and a fixed positive number of physical working levels. -/
@[expose] def scales (M : ℕ) (x : NCL.HWord.Instance q) : Scales.Parameters where
  axes := (StripSource.layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)).portCount + 1
  levels := M + 1
  axes_pos := Nat.le_add_left 1 _
  levels_pos := Nat.le_add_left 1 _

/-- The literal complete recipe of the original native drawing and normalized endpoint vectors. -/
@[expose] def recipe (M : ℕ) (x : NCL.HWord.Instance q) : SegmentRecipe :=
  (StripSource.layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)).canonicalRecipe
    (scales H hq M x)
    (StripSource.normalizedInitialAxes (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x))
    (StripSource.normalizedTargetAxes (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x))

/-- Every original contour port has its actual allocated physical axis. -/
theorem portCount_le_scales_axes (M : ℕ) (x : NCL.HWord.Instance q) :
    (StripSource.layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)).portCount ≤
      (scales H hq M x).axes := Nat.le_succ _

/-- The actual full compiled drawing fits the same fixed working-level budget on every word. -/
theorem highest_le_scales_levels (x : NCL.HWord.Instance q) :
    (StripSource.layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)).pages.highest ≤
      (scales H hq (levelBudget q) x).levels :=
  (StripSource.validDrawing_highest_le (native_valid H hq x) (native_validDrawing H hq x)).trans
    (Nat.le_succ _)

/-- The actual compiled port count determines the polynomial-time unary axis allocation. -/
theorem computableInPolyTime_scales_axes (M : ℕ) :
    ComputableInPolyTime (fun x => (scales H hq M x).axes) (NCL.HWord.encInstance q) encUnary := by
  have hl := (StripSource.computableInPolyTime_layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q)).comp
    (PushPuzzle.NCL.HWord.Strip.Sweep.computableInPolyTime_compile H hq)
  have hn := encPortLayout_portCount_polyTime hl
  change ComputableInPolyTime (fun x =>
    (StripSource.layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)).portCount + 1) _ _
  fun_prop

/-- At every fixed level allocation, the complete actual marked recipe is standard PT. -/
theorem computableInPolyTime_recipe (M : ℕ) :
    ComputableInPolyTime (recipe H hq M) (NCL.HWord.encInstance q) encSegmentRecipe := by
  have hn := PushPuzzle.NCL.HWord.Strip.Sweep.computableInPolyTime_compile H hq
  have hl := (StripSource.computableInPolyTime_layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q)).comp hn
  have hi := (StripSource.computableInPolyTime_normalizedInitialAxes
    (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q)).comp hn
  have ht := (StripSource.computableInPolyTime_normalizedTargetAxes
    (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q)).comp hn
  exact PortLayout.computableInPolyTime_canonicalRecipe hl
    (computableInPolyTime_scales_axes H hq M) (fun _ => rfl) hi ht

/-- Every cell of the actual fixed-alphabet output bitmap emits in standard polynomial time. -/
theorem computableInPolyTime_emit (M : ℕ) :
    ComputableInPolyTime (fun x => (recipe H hq M x).emit)
      (NCL.HWord.encInstance q) PushFS.Encoding.encData :=
  SegmentRecipe.computableInPolyTime_emit.comp (computableInPolyTime_recipe H hq M)

end PushPuzzle.PushS.WordSource
