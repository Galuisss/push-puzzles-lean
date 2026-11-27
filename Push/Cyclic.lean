/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScan
public import Push.CornerDockReverse
public import Push.Isometry

/-! A widened column-reader stage, southwest dock, and quarter turn for the next cyclic read. -/

@[expose] public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

/-- Reserve at least `w+2` empty room cells on every old auxiliary row. -/
def wideReader (r : ColumnScan.Input) : ColumnScan.Input := { r with extraWidth := r.width + 1 + r.extraWidth }

/-- The complete southwest dock attached to the widened first reader. -/
def dock (r : ColumnScan.Input) : CornerDock.Input where
  width := (wideReader r).outputWidth
  height := (wideReader r).outputHeight
  initial := (wideReader r).initialState
  goalY := ⟨(wideReader r).targetLevel,
    ((wideReader r).targetLevel_le_needleLevel ⟨0, (wideReader r).width_pos⟩).trans_lt
      ((wideReader r).needleLevel_lt_height _)⟩

/-- The docking input's source is exactly the same ordinary first-reader game. -/
theorem dock_source (r : ColumnScan.Input) : (dock r).source = (wideReader r).compile := by
  simp only [dock, CornerDock.Input.source, ColumnScan.Input.compile,
    CornerDock.Input.sourceGoal, ColumnScan.Input.target]

/-- The physical turn `(x,y) ↦ (y,width−1−x)`. -/
def turnGeometry (w h : ℕ) : GridIsometry w h h w :=
  (GridIsometry.reflectX w h).trans (GridIsometry.transpose w h)

/-- Rotate southwest to southeast, ready for another column-reader attachment. -/
def turn (I : Push.Instance) : Push.Instance := I.reflectedX.transposed

/-- The next live source game in the cyclic construction. -/
def nextSource (r : ColumnScan.Input) : Push.Instance := turn (dock r).compile

/-- Track an original source cell through the first reader, dock, and physical quarter turn. -/
def sourceEmbed (r : ColumnScan.Input) (q : Cell r.width r.height) :
    Cell (nextSource r).width (nextSource r).height :=
  (turnGeometry (dock r).outputWidth (dock r).outputHeight).cells
    ((dock r).embed ((wideReader r).embed q))

theorem sourceEmbed_injective (r : ColumnScan.Input) : Function.Injective (sourceEmbed r) := by
  intro p q he
  exact (wideReader r).embed_injective ((dock r).embed_injective
    ((turnGeometry _ _).cells.injective he))

/-- Original source rows become next-stage source columns. -/
theorem sourceEmbed_x (r : ColumnScan.Input) (q : Cell r.width r.height) :
    (sourceEmbed r q).1.val = q.2.val := rfl

/-- Reading the new column from below reads the old row from its western end. -/
theorem sourceEmbed_y (r : ColumnScan.Input) (q : Cell r.width r.height) :
    (sourceEmbed r q).2.val = (dock r).outputWidth - (q.1.val + 3) := by
  rfl

/-- The next live source's goal is its literal southeast corner. -/
theorem nextSource_target (r : ColumnScan.Input) :
    (nextSource r).target.1.val + 1 = (nextSource r).width ∧
      (nextSource r).target.2.val + 1 = (nextSource r).height := by
  have hw : 0 < (dock r).outputWidth := by dsimp [CornerDock.Input.outputWidth]; omega
  have hh : 0 < (dock r).outputHeight := by
    have := (dock r).height_pos
    dsimp [CornerDock.Input.outputHeight]
    omega
  change (dock r).outputHeight - 1 + 1 = (dock r).outputHeight ∧
    (dock r).outputWidth - (0 + 1) + 1 = (dock r).outputWidth
  omega

/-- Map a next western-read quota family to source rows and clear every old auxiliary row. -/
def nextQuotas (r : ColumnScan.Input) (rows : List ℕ) : List ℕ :=
  rows ++ List.replicate ((wideReader r).outputHeight - r.height) (r.width + 2) ++
    List.replicate ((dock r).outputHeight - (wideReader r).outputHeight) 0

theorem nextQuotas_length (r : ColumnScan.Input) (rows : List ℕ) (hlen : rows.length = r.height) :
    (nextQuotas r rows).length = (nextSource r).width := by
  have hreader : r.height ≤ (wideReader r).outputHeight := by
    change r.height ≤ r.height + (wideReader r).length
    omega
  have hdock : (wideReader r).outputHeight ≤ (dock r).outputHeight := by
    change (wideReader r).outputHeight ≤ (wideReader r).outputHeight + (dock r).distance
    omega
  simp only [nextQuotas, List.length_append, List.length_replicate, hlen]
  change r.height + ((wideReader r).outputHeight - r.height) +
    ((dock r).outputHeight - (wideReader r).outputHeight) = (dock r).outputHeight
  omega

end PushPuzzle.Push.Cyclic
