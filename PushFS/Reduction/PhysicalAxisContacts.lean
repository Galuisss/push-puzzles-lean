/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalAxisCharts

/-! Every real boundary rail point has an interior owner in its reciprocal neighbor. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles

open Cslib.Complexity.NCL Gadgets.Wires PhysicalBitmap GateTileRouting
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board

def NearSide (k : Key) : Direction→Cell (piece k).width (piece k).height→Prop
  | .north,p=>p.2.val<7
  | .east,p=>(piece k).width≤p.1.val+7
  | .south,p=>(piece k).height≤p.2.val+7
  | .west,p=>p.1.val<7

private theorem dimensions_pad (k : Key) :
    (piece k).width+2*pad k=200007 ∧(piece k).height+2*pad k=198068 := by
  cases k <;> exact ⟨rfl,rfl⟩

theorem port_level (k : Key) (d : Direction) (p : Cell (piece k).width (piece k).height)
    (hu : Used k d) (hf : NearSide k d p) (hr : (portName k d).Supports p) :
    (portName k d).level≤((classifier k).name p).level := by
  cases k with
  | inl g=>
    have hw : (piece (.inl g)).width=200007:=rfl
    have hh : (piece (.inl g)).height=198068:=rfl
    apply FullGateStatics.classifier_port_level g d hu p
    · cases d <;> dsimp only [NearSide,FullGateBoundary.InFrame,hw,hh] at hf ⊢ <;> omega
    · exact hr
  | inr a=>
    have hw : (piece (.inr a)).width=200005:=rfl
    have hh : (piece (.inr a)).height=198066:=rfl
    have hc : Catalog.InCollar (face d) p := by
      cases d <;> dsimp only [NearSide,face,Catalog.InCollar,hw,hh] at hf ⊢ <;> omega
    have hn:=Catalog.axisTracks_collar a.1 a.2.1 a.2.2 (face d) p hc
    have hu' : Catalog.FaceUsed a.1 (face d):=hu
    rw [ite_eq_left hu'] at hn
    have ht : Catalog.collarName (face d) p=portName (.inr a) d := by
      cases d <;> dsimp only [portName,pad,AxisTrack.Supports] at hr <;>
        simp only [face,Catalog.collarName,hr,ite_true,portName,pad]
    change (portName (.inr a) d).level≤((Catalog.axisTracks a.1 a.2.1 a.2.2).name p).level
    rw [hn,ht]

structure PortContact (p r : GridRouting.Point) (k l : Key) (d : Direction)
    (q : Cell (piece k).width (piece k).height) where
  cell : Cell (piece l).width (piece l).height
  interior : Interior cell
  coordinates : coordinates r l cell=coordinates p k q
  collar : NearSide l d.opposite cell
  rail : (portName l d.opposite).Supports cell

theorem port_contact (p r : GridRouting.Point) (k l : Key) (d : Direction)
    (hn : neighbor d p=some r) (q : Cell (piece k).width (piece k).height)
    (hs : OnSide k d q) (hr : (portName k d).Supports q) :
    Nonempty (PortContact p r k l d q) := by
  have hk:=dimensions_pad k
  have hl:=dimensions_pad l
  have hpk:=pad_le_one k
  have hpl:=pad_le_one l
  have hx:=q.1.isLt
  have hy:=q.2.isLt
  let x:=(coordinates p k q).1-(offset r l).1
  let y:=(coordinates p k q).2-(offset r l).2
  have hb : (offset r l).1≤(coordinates p k q).1 ∧
      (offset r l).2≤(coordinates p k q).2 ∧
      0<x ∧x+1<(piece l).width ∧0<y ∧y+1<(piece l).height := by
    cases d <;> dsimp only [neighbor] at hn
    all_goals try split_ifs at hn
    all_goals simp only [Option.some.injEq,Prod.ext_iff] at hn
    all_goals dsimp only [x,y,coordinates,offset,OnSide,portName,AxisTrack.Supports,strideX,strideY] at hs hr ⊢
    all_goals omega
  let s : Cell (piece l).width (piece l).height := (⟨x,by omega⟩,⟨y,by omega⟩)
  refine ⟨⟨s,⟨hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2.1,hb.2.2.2.2.2⟩,?_,?_,?_⟩⟩
  · dsimp only [coordinates] at hb
    apply Prod.ext <;> dsimp only [coordinates,s,x,y] <;> omega
  all_goals
    cases d <;> dsimp only [neighbor] at hn
    all_goals try split_ifs at hn
    all_goals simp only [Option.some.injEq,Prod.ext_iff] at hn
    all_goals dsimp only [s,x,y,coordinates,offset,OnSide,portName,AxisTrack.Supports,NearSide,
      Direction.opposite,strideX,strideY] at hs hr ⊢
    all_goals omega

end PushPuzzle.PushFS.Reduction.PhysicalTiles
