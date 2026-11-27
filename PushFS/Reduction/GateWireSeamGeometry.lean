/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.FullGateStatics.Outer
public import PushFS.Reduction.PhysicalWireSeamGeometry
public import PushFS.Gadgets.Gates.StaticSlots

/-! Literal complete-gate exterior ribbon paths and the incoming one-cell threshold correction. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.GateWireGeometry

open Gadgets Gadgets.Wires Catalog PhysicalBitmap GateTileRouting FullGateStatics
set_option maxRecDepth 65536
set_option maxHeartbeats 200000

def gatePoint (p : NCL.GridRouting.Point) (q : ℕ×ℕ) : ℕ×ℕ :=
  (strideX*p.1+q.1,strideY*p.2+q.2)

def ribbonGate (d : Direction) (inc a : Bool) : Cell (ribbonWidth d) (ribbonHeight d) :=
  match d with
  | .west=>(⟨5-inc.toNat-a.toNat,by cases inc <;> cases a <;> decide⟩,⟨2,by decide⟩)
  | .east=>(⟨1+inc.toNat+a.toNat,by cases inc <;> cases a <;> decide⟩,⟨2,by decide⟩)
  | .north=>(⟨2,by decide⟩,⟨5-inc.toNat-a.toNat,by cases inc <;> cases a <;> decide⟩)
  | .south=>(⟨2,by decide⟩,⟨1+inc.toNat+a.toNat,by cases inc <;> cases a <;> decide⟩)

def ribbonWire (d : Direction) (inc a : Bool) : Cell (ribbonWidth d) (ribbonHeight d) :=
  match d with
  | .west=>(⟨3-inc.toNat-a.toNat,by cases inc <;> cases a <;> decide⟩,⟨2,by decide⟩)
  | .east=>(⟨3+inc.toNat+a.toNat,by cases inc <;> cases a <;> decide⟩,⟨2,by decide⟩)
  | .north=>(⟨2,by decide⟩,⟨3-inc.toNat-a.toNat,by cases inc <;> cases a <;> decide⟩)
  | .south=>(⟨2,by decide⟩,⟨3+inc.toNat+a.toNat,by cases inc <;> cases a <;> decide⟩)

private theorem ribbon_paths : ∀(d : Direction) (inc a : Bool),
    Gates.staticRun (ribbonWall d) (ribbonGate d inc a) [d,d]=some (ribbonWire d inc a) ∧
    Gates.staticRun (ribbonWall d) (ribbonWire d inc a) [d.opposite,d.opposite]=some (ribbonGate d inc a) := by decide +kernel

theorem ribbon_component (d : Direction) (inc a : Bool) :
    SameComponent (ribbonBoard d) (ribbonGate d inc a) (ribbonWire d inc a) :=
  ⟨Gates.staticRun_sound (ribbon_wall_correct d) (ribbon_paths d inc a).1,
    Gates.staticRun_sound (ribbon_wall_correct d) (ribbon_paths d inc a).2⟩

theorem ribbon_gate_coordinates : ∀(d : Direction) (inc a : Bool),
    let p:=(ribbonChart d).embedding.cells (ribbonGate d inc a)
    (p.1.val,p.2.val)=FullGateBoundary.endpointPoint d inc a false := by decide +kernel

def wireGhost : Direction→Bool→Bool→ℕ×ℕ
  | .west,inc,a=>(3-inc.toNat-a.toNat,99034)
  | .east,inc,a=>(200003+inc.toNat+a.toNat,99034)
  | .north,inc,a=>(100003,3-inc.toNat-a.toNat)
  | .south,inc,a=>(100003,198064+inc.toNat+a.toNat)

private theorem ribbon_wire_coordinates : ∀(d : Direction) (inc a : Bool),
    let p:=(ribbonChart d).embedding.cells (ribbonWire d inc a)
    (p.1.val,p.2.val)=wireGhost d inc a := by decide +kernel

def wireEndpoint (inc : Bool) (k : Catalog.Kind) (a : Bool) : Catalog.Cell :=
  if inc then Catalog.lastPoint k a else Catalog.firstPoint k a

def Flow (d : Direction) (inc : Bool) (k : Catalog.Kind) : Prop :=
  if inc then Catalog.targetDirection k=d.opposite else Catalog.sourceDirection k=d

private theorem geometry (p r : NCL.GridRouting.Point) (d : Direction) (inc a : Bool) (k : Catalog.Kind)
    (hk : Catalog.Straight k) (hn : neighbor d p=some r) (hd : Flow d inc k) :
    let b:=if inc then !a else a
    let q:=(ribbonChart d).embedding.cells (ribbonWire d inc b)
    gatePoint p (q.1.val,q.2.val)=PhysicalTiles.wirePoint r (wireEndpoint inc k a) ∧
    DirectionalStep d (gatePoint p (FullGateBoundary.endpointPoint d inc b false))
      (PhysicalTiles.wirePoint r (wireEndpoint inc k a)) := by
  dsimp only
  rw [ribbon_wire_coordinates]
  rcases hk with rfl|rfl|rfl
  all_goals cases d <;> cases inc <;> cases a
  all_goals simp only [Flow,Catalog.sourceDirection,Catalog.targetDirection,Direction.opposite,
    Bool.false_eq_true,ite_false,ite_true] at hd
  all_goals cases hd
  all_goals dsimp only [neighbor] at hn
  all_goals try split_ifs at hn
  all_goals simp only [Option.some.injEq,Prod.ext_iff] at hn
  all_goals constructor
  all_goals try apply Prod.ext
  all_goals dsimp only [gatePoint,PhysicalTiles.wirePoint,wireEndpoint,FullGateBoundary.endpointPoint,
    wireGhost,
    Catalog.firstPoint,Catalog.lastPoint,GridEmbedding.translate,Catalog.width,Catalog.height,DirectionalStep,Bool.toNat_false,Bool.toNat_true,
    Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_true,ite_false,strideX,strideY]
  all_goals simp only [Bool.false_eq_true,reduceIte,Bool.not_false,Bool.not_true,Bool.toNat_false,Bool.toNat_true] at *
  all_goals dsimp at *
  all_goals omega

theorem ghost_coordinates (p r : NCL.GridRouting.Point) (d : Direction) (inc a : Bool) (k : Catalog.Kind)
    (hk : Catalog.Straight k) (hn : neighbor d p=some r) (hd : Flow d inc k) :
    let b:=if inc then !a else a
    let q:=(ribbonChart d).embedding.cells (ribbonWire d inc b)
    gatePoint p (q.1.val,q.2.val)=PhysicalTiles.wirePoint r (wireEndpoint inc k a) :=
  (geometry p r d inc a k hk hn hd).1

theorem source_step (p r : NCL.GridRouting.Point) (d : Direction) (inc a : Bool) (k : Catalog.Kind)
    (hk : Catalog.Straight k) (hn : neighbor d p=some r) (hd : Flow d inc k) :
    DirectionalStep d (gatePoint p (FullGateBoundary.endpointPoint d inc (if inc then !a else a) false))
      (PhysicalTiles.wirePoint r (wireEndpoint inc k a)) :=
  (geometry p r d inc a k hk hn hd).2

theorem incoming_exclusive (p r : NCL.GridRouting.Point) (d : Direction) (k : Catalog.Kind)
    (hk : Catalog.Straight k) (hn : neighbor d p=some r) (hd : Flow d true k)
    (x y : ℕ×ℕ)
    (hgap : DirectionalGap d x y)
    (hx : TravelHigh d (gatePoint p (FullGateBoundary.endpointPoint d true true false)) x)
    (hy : TravelHigh d.opposite (PhysicalTiles.wirePoint r (Catalog.lastPoint k true)) y) : False := by
  rcases hk with rfl|rfl|rfl
  all_goals cases d
  all_goals simp only [Flow,Catalog.targetDirection,Direction.opposite,ite_true] at hd
  all_goals cases hd
  all_goals dsimp only [neighbor] at hn
  all_goals try split_ifs at hn
  all_goals simp only [Option.some.injEq,Prod.ext_iff] at hn
  all_goals dsimp only [DirectionalGap,TravelHigh,gatePoint,PhysicalTiles.wirePoint,
    FullGateBoundary.endpointPoint,Catalog.lastPoint,Direction.opposite,Bool.toNat_true,
    Bool.false_eq_true,ite_false,strideX,strideY] at *
  all_goals simp only [Bool.false_eq_true,reduceIte] at *
  all_goals dsimp at *
  all_goals omega
end PushPuzzle.PushFS.Reduction.GateWireGeometry
