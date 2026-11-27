/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalNear

/-! Canonical slot gaps across the actual physical source-cell seams exclude adjacency. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles.SlotSeparation


open Cslib.Complexity.NCL Gadgets.Wires PhysicalBitmap
set_option maxHeartbeats 2000000

theorem wire_east (k l : Catalog.Kind) (a : Bool) (p r : GridRouting.Point)
    (hp : Catalog.SlotBounds k a p.1 p.2) (hr : Catalog.SlotBounds l a r.1 r.2)
    (hf : CellPlan.Consecutive k l .east) : ¬Nearby 1 p (strideX+r.1,r.2) := by
  intro he
  dsimp only [Nearby,strideX] at he
  cases k <;> cases l <;> cases a
  all_goals simp only [CellPlan.Consecutive,Catalog.sourceDirection,Catalog.targetDirection,
    Direction.opposite,reduceCtorEq,and_true,and_false,or_true,or_false] at hf
  all_goals simp only [Catalog.SlotBounds,Bool.toNat_false,Bool.toNat_true] at hp hr
  all_goals omega

theorem wire_south (k l : Catalog.Kind) (a : Bool) (p r : GridRouting.Point)
    (hp : Catalog.SlotBounds k a p.1 p.2) (hr : Catalog.SlotBounds l a r.1 r.2)
    (hf : CellPlan.Consecutive k l .south) : ¬Nearby 1 p (r.1,strideY+r.2) := by
  intro he
  dsimp only [Nearby,strideY] at he
  cases k <;> cases l <;> cases a
  all_goals simp only [CellPlan.Consecutive,Catalog.sourceDirection,Catalog.targetDirection,
    Direction.opposite,reduceCtorEq,and_true,and_false,or_false] at hf
  all_goals simp only [Catalog.SlotBounds,Bool.toNat_false,Bool.toNat_true] at hp hr
  all_goals omega

theorem gate_wire (d : Direction) (inc a prev : Bool) (k : Catalog.Kind)
    (p r t : GridRouting.Point) (hn : neighbor d p=some r)
    (ht : Catalog.SlotBounds k a t.1 t.2)
    (hf : if inc then Catalog.targetDirection k=d.opposite else Catalog.sourceDirection k=d) :
    ¬Nearby 1
      (strideX*p.1+(GateTileRouting.FullGateBoundary.endpointPoint d inc (if inc then !a else a) prev).1,
        strideY*p.2+(GateTileRouting.FullGateBoundary.endpointPoint d inc (if inc then !a else a) prev).2)
      (strideX*r.1+1+t.1,strideY*r.2+1+t.2) := by
  intro he
  dsimp only [Nearby] at he
  cases d <;> cases inc <;> cases a <;> cases prev <;> cases k
  all_goals simp only [Catalog.sourceDirection,Catalog.targetDirection,Direction.opposite,
    Bool.false_eq_true,ite_true,ite_false,reduceCtorEq] at hf
  all_goals simp only [Catalog.SlotBounds,Bool.toNat_false,Bool.toNat_true] at ht
  all_goals dsimp only [neighbor] at hn
  all_goals simp [GateTileRouting.FullGateBoundary.endpointPoint,strideX,strideY] at he
  all_goals try split_ifs at hn
  all_goals simp only [Option.some.injEq,Prod.ext_iff] at hn
  all_goals omega

theorem wire_six_face (k : Catalog.Kind) (a : Bool) (f : Catalog.Face) (p : Catalog.Cell)
    (hb : Catalog.SlotRegion k a p) (hf : Catalog.InFace6 f p) : Catalog.FaceUsed k f := by
  cases k <;> cases f <;> cases a <;>
    simp_all [Catalog.SlotRegion,Catalog.SlotBounds,Catalog.InFace6,Catalog.FaceUsed,Catalog.sourceFace,Catalog.targetFace] <;> omega

end PushPuzzle.PushFS.Reduction.PhysicalTiles.SlotSeparation
