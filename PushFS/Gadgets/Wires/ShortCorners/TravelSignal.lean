/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.ShortCorners.RotatedSignal
public import PushFS.Gadgets.Wires.Catalog.RectThresholds

/-! Protected short-corner signals read at their actual true-phase physical endpoint cells. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.ShortCorners

open Catalog Soundness

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}

def thresholdCell (k : Kind) (o : RectOrientation) (a b : Bool)
    (g : StorageImage M ((slotMatching k a b).reorient ((o.axis (width k) (height k)).geometry)))
    (l : Fin (count k)) : Cell I.width I.height :=
  (GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells
    ((o.axis (width k) (height k)).geometry.cells ((template k).position true l))

private theorem sourceHigh_iff_travel (k : Kind) (o : RectOrientation) (a b : Bool)
    (g : StorageImage M ((slotMatching k a b).reorient ((o.axis (width k) (height k)).geometry)))
    (p : Cell I.width I.height) :
    sourceHigh k o g.dx g.dy p ↔TravelHigh (o.direction .west)
      ((thresholdCell k o a b g (first k)).1.val,(thresholdCell k o a b g (first k)).2.val) (p.1.val,p.2.val) := by
  have he:=congrArg (fun p : Cell (o.width I.width I.height) (o.height I.width I.height)=>p.1.val) (o.undo_cells I.width I.height (width k) (height k) g.dx g.dy
    g.fit_x g.fit_y ((template k).position true (first k)))
  change ((o.undo I.width I.height).cells (thresholdCell k o a b g (first k))).1.val=
    (o.undoOffset I.width I.height (width k) (height k) g.dx g.dy).1+((template k).position true (first k)).1.val at he
  have hx:=(endpoints k true).1
  simp only [Bool.toNat_true] at hx
  apply Iff.trans ?_ (undo_west_iff o (thresholdCell k o a b g (first k)) p)
  unfold sourceHigh
  omega

private theorem targetHigh_iff_travel (k : Kind) (o : RectOrientation) (a b : Bool)
    (g : StorageImage M ((slotMatching k a b).reorient ((o.axis (width k) (height k)).geometry)))
    (p : Cell I.width I.height) :
    targetHigh k o g.dx g.dy p ↔TravelHigh (o.direction .south)
      ((thresholdCell k o a b g (last k)).1.val,(thresholdCell k o a b g (last k)).2.val) (p.1.val,p.2.val) := by
  have he:=congrArg (fun p : Cell (o.width I.width I.height) (o.height I.width I.height)=>p.2.val) (o.undo_cells I.width I.height (width k) (height k) g.dx g.dy
    g.fit_x g.fit_y ((template k).position true (last k)))
  change ((o.undo I.width I.height).cells (thresholdCell k o a b g (last k))).2.val=
    (o.undoOffset I.width I.height (width k) (height k) g.dx g.dy).2+((template k).position true (last k)).2.val at he
  have hy:=(endpoints k true).2.2.2
  simp only [Bool.toNat_true] at hy
  apply Iff.trans ?_ (undo_south_iff o (thresholdCell k o a b g (last k)) p)
  unfold targetHigh
  omega

/-- The actual first endpoint at its true-phase threshold forces the actual last endpoint's true-phase threshold. -/
theorem travel_signal (k : Kind) (o : RectOrientation) (a b : Bool)
    (g : StorageImage M ((slotMatching k a b).reorient ((o.axis (width k) (height k)).geometry)))
    {S T : LabelledState L I.width I.height} (hs : Successful M S T) (cert : Certificate I) (ordered : M.Ordered)
    (hin : TravelHigh (o.direction .west)
      ((thresholdCell k o a b g (first k)).1.val,(thresholdCell k o a b g (first k)).2.val)
      ((S.position (g.labels (first k))).1.val,(S.position (g.labels (first k))).2.val)) :
    TravelHigh (o.direction .south)
      ((thresholdCell k o a b g (last k)).1.val,(thresholdCell k o a b g (last k)).2.val)
      ((S.position (g.labels (last k))).1.val,(S.position (g.labels (last k))).2.val) :=
  (targetHigh_iff_travel k o a b g _).mp
    (rotated_signal k o a b g hs cert ordered ((sourceHigh_iff_travel k o a b g _).mpr hin))

end PushPuzzle.PushFS.Gadgets.Wires.ShortCorners
