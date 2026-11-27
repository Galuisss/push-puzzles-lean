/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Primitive
public import PushFS.Reduction.FullGateStatics.Outer
public import PushFS.Reduction.FullGateStatics.PhaseWalls

/-! Executable wall-free metadata for the true local static chart endpoints. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory Gadgets Gadgets.Wires
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

abbrev ChartIndex (g : GateTileState) := Inventory.Index g ⊕Fin 3

def rawChart (g : GateTileState) : ChartIndex g→TranslatedAxisChart 200007 198068
  | .inl i => primitiveChart g i
  | .inr role => outerChart g role

private theorem raw_chart_walls (g : GateTileState) (c : ChartIndex g) :
    (rawChart g c).embedding.WallsAgree (rawChart g c).board (fullPuzzle g).board := by
  cases c with
  | inl i => exact primitive_walls g i
  | inr role => exact outer_walls g role

def chart (g : GateTileState) (c : ChartIndex g) : TranslatedAxisChart 200007 198068 :=
  rawChart (ofGeometry (geometry g)) c

theorem chart_walls (g : GateTileState) (c : ChartIndex g) :
    (chart g c).embedding.WallsAgree (chart g c).board (fullPuzzle g).board := by
  intro p
  have hh:=raw_chart_walls (ofGeometry (geometry g)) c p
  have he:=congrArg (fun walls=>((chart g c).embedding.cells p)∈walls) (full_walls_geometry g)
  exact (Iff.of_eq he).symm.trans hh

def chartIndices (g : GateTileState) : List (ChartIndex g) :=
  (Inventory.indices g).map Sum.inl++(List.finRange 3).map Sum.inr

theorem mem_chartIndices (g : GateTileState) (c : ChartIndex g) : c∈chartIndices g := by
  cases c with
  | inl i => exact List.mem_append_left _ (List.mem_map.mpr ⟨i,Inventory.mem_indices g i,rfl⟩)
  | inr role => exact List.mem_append_right _ (List.mem_map.mpr ⟨role,by simp,rfl⟩)

structure Shape where
  width : ℕ
  height : ℕ
  dx : ℕ
  dy : ℕ
  name : (ℕ×ℕ)→AxisTrack

def shape (C : TranslatedAxisChart 200007 198068) : Shape where
  width:=C.width
  height:=C.height
  dx:=C.dx
  dy:=C.dy
  name p:=if hx : p.1<C.width then if hy : p.2<C.height then C.classifier.name (⟨p.1,hx⟩,⟨p.2,hy⟩) else .outside else .outside

theorem shape_name (C : TranslatedAxisChart 200007 198068) (p : Cell C.width C.height) :
    (shape C).name (p.1.val,p.2.val)=C.classifier.name p := by
  simp only [shape,p.1.isLt,p.2.isLt,dite_true]

def Shape.Contains (s : Shape) (p : ℕ×ℕ) : Prop :=
  s.dx≤p.1 ∧p.1<s.dx+s.width ∧s.dy≤p.2 ∧p.2<s.dy+s.height
instance (s : Shape) (p : ℕ×ℕ) : Decidable (s.Contains p) := by unfold Shape.Contains; infer_instance

def Shape.local (s : Shape) (p : ℕ×ℕ) : ℕ×ℕ := (p.1-s.dx,p.2-s.dy)
def Shape.global (s : Shape) (p : ℕ×ℕ) : ℕ×ℕ := (s.dx+p.1,s.dy+p.2)

def Shape.Safe (s : Shape) (p : ℕ×ℕ) : Prop :=
  (s.dx=0 ∨0<p.1) ∧(s.dx+s.width=200007 ∨p.1+1<s.width) ∧
    (s.dy=0 ∨0<p.2) ∧(s.dy+s.height=198068 ∨p.2+1<s.height)
instance (s : Shape) (p : ℕ×ℕ) : Decidable (s.Safe p) := by unfold Shape.Safe; infer_instance

def Shape.perimeter (s : Shape) : List (ℕ×ℕ) :=
  (((List.range s.width).map (fun x=>(x,0)) ++(List.range s.width).map (fun x=>(x,s.height-1))) ++
    (List.range s.height).map (fun y=>(0,y))) ++(List.range s.height).map (fun y=>(s.width-1,y))

def Shape.boundary (s : Shape) : List (ℕ×ℕ) :=
  if s.width=21 then [(10,0),(10,s.height-1)]
  else if s.height=21 then [(0,10),(s.width-1,10)] else s.perimeter

private theorem shape_geometry (g : GateTileState) (c : ChartIndex g) :
    shape (chart (ofGeometry (geometry g)) c)=shape (chart g c) := rfl

def safeAlternative {Idx : Type} (shapes : Idx→Shape) (p : ℕ×ℕ) (level : ℕ) (d : Idx) : Bool :=
  let s:=shapes d
  decide (s.Contains p ∧s.Safe (s.local p) ∧level≤(s.name (s.local p)).level)

def endpointTest {Idx : Type} (indices : List Idx) (shapes : Idx→Shape) (c : Idx) (u : ℕ×ℕ) : Bool :=
  let s:=shapes c
  if s.name u=.outside ∨s.Safe u then true
  else indices.any (safeAlternative shapes (s.global u) (s.name u).level)

def coverageShapes {Idx : Type} (indices : List Idx) (shapes : Idx→Shape) : Bool :=
  indices.all fun c=>(shapes c).boundary.all (endpointTest indices shapes c)

def coverageTest (g : GateTileState) : Bool :=
  coverageShapes (chartIndices g) (fun c=>shape (chart g c))

theorem coverage_geometry (g : GateTileState) : coverageTest (ofGeometry (geometry g))=coverageTest g := by
  change coverageShapes (chartIndices g) (fun c=>shape (chart (ofGeometry (geometry g)) c))=
    coverageShapes (chartIndices g) (fun c=>shape (chart g c))
  rw [funext (shape_geometry g)]

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
