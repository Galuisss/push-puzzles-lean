/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalNeighbors
public import PushFS.Gadgets.Wires.Catalog.SignalJoins
public import PushFS.Gadgets.Wires.Catalog.SlotCoordinates

/-! Exact ordinary-macrocell port anchors, source order and true-phase threshold spacing. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles

open Cslib.Complexity.NCL Gadgets.Wires Catalog PhysicalBitmap
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

def wirePoint (p : GridRouting.Point) (q : Catalog.Cell) : ℕ×ℕ :=
  (strideX*p.1+1+q.1.val,strideY*p.2+1+q.2.val)

theorem wire_seam_ghost (p r : GridRouting.Point) (k l : Catalog.Kind)
    (hn : neighbor (Catalog.targetDirection k) p=some r)
    (hd : Catalog.sourceDirection l=Catalog.targetDirection k) :
    wirePoint p (Catalog.faceCell (Catalog.targetFace k) (2,10))=wirePoint r (Catalog.firstPoint l false) := by
  cases k <;> cases l
  all_goals simp only [Catalog.sourceDirection,Catalog.targetDirection] at hd
  all_goals cases hd
  all_goals dsimp only [Catalog.targetDirection,neighbor] at hn
  all_goals try split_ifs at hn
  all_goals simp only [Option.some.injEq,Prod.ext_iff] at hn
  all_goals apply Prod.ext
  all_goals dsimp only [wirePoint,Catalog.faceCell,Catalog.targetFace,Catalog.firstPoint,strideX,strideY,Catalog.width,Catalog.height,Bool.toNat_false,Bool.toNat_true]
  all_goals omega

theorem wire_seam_order (p r : GridRouting.Point) (k l : Catalog.Kind) (a c : Bool)
    (hn : neighbor (Catalog.targetDirection k) p=some r)
    (hd : Catalog.sourceDirection l=Catalog.targetDirection k) :
    DirectionalOrder (Catalog.targetDirection k) (wirePoint p (Catalog.lastPoint k a)) (wirePoint r (Catalog.firstPoint l c)) := by
  have ha : a.toNat≤1:=by cases a <;> decide
  have hc : c.toNat≤1:=by cases c <;> decide
  cases k <;> cases l
  all_goals simp only [Catalog.sourceDirection,Catalog.targetDirection] at hd
  all_goals cases hd
  all_goals dsimp only [Catalog.targetDirection,neighbor] at hn
  all_goals try split_ifs at hn
  all_goals simp only [Option.some.injEq,Prod.ext_iff] at hn
  all_goals dsimp only [DirectionalOrder,wirePoint,Catalog.targetDirection,Catalog.lastPoint,Catalog.firstPoint,strideX,strideY,Catalog.width,Catalog.height,Bool.toNat_false,Bool.toNat_true]
  all_goals omega

theorem wire_seam_true_step (p r : GridRouting.Point) (k l : Catalog.Kind)
    (hn : neighbor (Catalog.targetDirection k) p=some r)
    (hd : Catalog.sourceDirection l=Catalog.targetDirection k) :
    DirectionalStep (Catalog.targetDirection k) (wirePoint p (Catalog.lastPoint k true)) (wirePoint r (Catalog.firstPoint l true)) := by
  cases k <;> cases l
  all_goals simp only [Catalog.sourceDirection,Catalog.targetDirection] at hd
  all_goals cases hd
  all_goals dsimp only [Catalog.targetDirection,neighbor] at hn
  all_goals try split_ifs at hn
  all_goals simp only [Option.some.injEq,Prod.ext_iff] at hn
  all_goals dsimp only [DirectionalStep,wirePoint,Catalog.targetDirection,Catalog.lastPoint,Catalog.firstPoint,strideX,strideY,Catalog.width,Catalog.height,Bool.toNat_false,Bool.toNat_true]
  all_goals omega

end PushPuzzle.PushFS.Reduction.PhysicalTiles
