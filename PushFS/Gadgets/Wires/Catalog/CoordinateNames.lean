/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.Statics
public import PushFS.Gadgets.Wires.Catalog.BoundaryWalls

/-! Literal coordinate names of the seven complete ordinary physical cells. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

def coordinateName (k : Kind) (p : Cell) : AxisTrack :=
  match k with
  | .east | .west => if p.2.val=99033 then .horizontal 99033 else .outside
  | .south => if p.1.val=100002 then .vertical 100002 else .outside
  | .westSouth | .eastSouth | .southEast | .southWest =>
    if p.1.val=100002 ∧p.2.val=99033 then .sink 100002 99033
    else if p.2.val=99033 ∧(if k=.westSouth ∨k=.southEast then 100002<p.1.val else p.1.val<100002)
      then .horizontal 99033
    else if p.1.val=100002 ∧(if k=.westSouth ∨k=.eastSouth then 99033<p.2.val else p.2.val<99033)
      then .vertical 100002
    else .outside

private theorem native_name (k : Kind) (a b : Bool)
    (q : PushFS.Cell (base k a b).width (base k a b).height) :
    AxisTrack.shift (dx k) (dy k) ((baseStrong k a b).axes.name q)=
      coordinateName k ((GridEmbedding.translate (dx k) (dy k) (fitsX k a b) (fitsY k a b)).cells q) := by
  cases k
  · change PushFS.Cell 200005 21 at q
    change AxisTrack.shift 0 99023 (if q.2.val=10 then .horizontal 10 else .outside)=
      (if 99023+q.2.val=99033 then .horizontal 99033 else .outside)
    have he : 99023+q.2.val=99033 ↔q.2.val=10:=by omega
    simp only [he]
    split_ifs <;> rfl
  · change PushFS.Cell 200005 21 at q
    change AxisTrack.shift 0 99023 ((AxisIsometry.reflectX 200005 21).name
      (if q.2.val=10 then .horizontal 10 else .outside))=
      (if 99023+q.2.val=99033 then .horizontal 99033 else .outside)
    have he : 99023+q.2.val=99033 ↔q.2.val=10:=by omega
    simp only [he]
    split_ifs <;> rfl
  · change PushFS.Cell 21 198066 at q
    change AxisTrack.shift 99992 0 ((AxisIsometry.reflectX 21 198066).name
      ((AxisIsometry.transpose 198066 21).name
      (if 21-(q.1.val+1)=10 then .horizontal 10 else .outside)))=
      (if 99992+q.1.val=100002 then .vertical 100002 else .outside)
    have hx : q.1.val<21:=q.1.isLt
    split_ifs <;> simp_all [AxisTrack.shift,AxisIsometry.reflectX,AxisIsometry.transpose] <;> omega
  · change PushFS.Cell 100013 99043 at q
    change AxisTrack.shift 99992 99023
      (if q.1.val=10 ∧q.2.val=10 then .sink 10 10
      else if q.2.val=10 ∧10<q.1.val then .horizontal 10
      else if q.1.val=10 ∧10<q.2.val then .vertical 10 else .outside)=
      (if 99992+q.1.val=100002 ∧99023+q.2.val=99033 then .sink 100002 99033
      else if 99023+q.2.val=99033 ∧100002<99992+q.1.val then .horizontal 99033
      else if 99992+q.1.val=100002 ∧99033<99023+q.2.val then .vertical 100002 else .outside)
    split_ifs <;> simp_all [AxisTrack.shift] <;> omega
  · change PushFS.Cell 100013 99043 at q
    change AxisTrack.shift 0 99023 ((AxisIsometry.reflectX 100013 99043).name
      (if 100013-(q.1.val+1)=10 ∧q.2.val=10 then .sink 10 10
      else if q.2.val=10 ∧10<100013-(q.1.val+1) then .horizontal 10
      else if 100013-(q.1.val+1)=10 ∧10<q.2.val then .vertical 10 else .outside))=
      (if 0+q.1.val=100002 ∧99023+q.2.val=99033 then .sink 100002 99033
      else if 99023+q.2.val=99033 ∧0+q.1.val<100002 then .horizontal 99033
      else if 0+q.1.val=100002 ∧99033<99023+q.2.val then .vertical 100002 else .outside)
    have hx : q.1.val<100013:=q.1.isLt
    have hxe : 100013-(q.1.val+1)=10 ↔q.1.val=100002:=by omega
    have hxl : 10<100013-(q.1.val+1) ↔q.1.val<100002:=by omega
    have hye : 99023+q.2.val=99033 ↔q.2.val=10:=by omega
    have hyl : 99033<99023+q.2.val ↔10<q.2.val:=by omega
    simp only [hxe,hxl,hye,hyl,Nat.zero_add]
    split_ifs <;> simp_all [AxisTrack.shift,AxisIsometry.reflectX]
  · change PushFS.Cell 100013 99044 at q
    change AxisTrack.shift 99992 0 ((AxisIsometry.transpose 99044 100013).name
      ((AxisIsometry.reflectX 99044 100013).name
      (if 99044-(q.2.val+1)=10 ∧q.1.val=10 then .sink 10 10
      else if q.1.val=10 ∧10<99044-(q.2.val+1) then .horizontal 10
      else if 99044-(q.2.val+1)=10 ∧10<q.1.val then .vertical 10 else .outside)))=
      (if 99992+q.1.val=100002 ∧0+q.2.val=99033 then .sink 100002 99033
      else if 0+q.2.val=99033 ∧100002<99992+q.1.val then .horizontal 99033
      else if 99992+q.1.val=100002 ∧0+q.2.val<99033 then .vertical 100002 else .outside)
    have hy : q.2.val<99044:=q.2.isLt
    have hxe : 99992+q.1.val=100002 ↔q.1.val=10:=by omega
    have hxl : 100002<99992+q.1.val ↔10<q.1.val:=by omega
    have hye : 99044-(q.2.val+1)=10 ↔q.2.val=99033:=by omega
    have hyl : 10<99044-(q.2.val+1) ↔q.2.val<99033:=by omega
    simp only [hxe,hxl,hye,hyl,Nat.zero_add]
    split_ifs <;> simp_all [AxisTrack.shift,AxisIsometry.reflectX,AxisIsometry.transpose]
  · change PushFS.Cell 100013 99044 at q
    change AxisTrack.shift 0 0 ((AxisIsometry.reflectX 100013 99044).name
      ((AxisIsometry.transpose 99044 100013).name ((AxisIsometry.reflectX 99044 100013).name
      (if 99044-(q.2.val+1)=10 ∧100013-(q.1.val+1)=10 then .sink 10 10
      else if 100013-(q.1.val+1)=10 ∧10<99044-(q.2.val+1) then .horizontal 10
      else if 99044-(q.2.val+1)=10 ∧10<100013-(q.1.val+1) then .vertical 10 else .outside))))=
      (if 0+q.1.val=100002 ∧0+q.2.val=99033 then .sink 100002 99033
      else if 0+q.2.val=99033 ∧0+q.1.val<100002 then .horizontal 99033
      else if 0+q.1.val=100002 ∧0+q.2.val<99033 then .vertical 100002 else .outside)
    have hx : q.1.val<100013:=q.1.isLt
    have hy : q.2.val<99044:=q.2.isLt
    have hxe : 100013-(q.1.val+1)=10 ↔q.1.val=100002:=by omega
    have hxl : 10<100013-(q.1.val+1) ↔q.1.val<100002:=by omega
    have hye : 99044-(q.2.val+1)=10 ↔q.2.val=99033:=by omega
    have hyl : 10<99044-(q.2.val+1) ↔q.2.val<99033:=by omega
    simp only [hxe,hxl,hye,hyl,Nat.zero_add]
    split_ifs <;> simp_all [AxisTrack.shift,AxisIsometry.reflectX,AxisIsometry.transpose]

private theorem axisTracks_name (k : Kind) (a b : Bool) (p : Cell) :
    (axisTracks k a b).name p=coordinateName k p := by
  classical
  let e:=GridEmbedding.translate (dx k) (dy k) (fitsX k a b) (fitsY k a b)
  by_cases hp : ∃q,e.cells q=p
  · obtain ⟨q,rfl⟩:=hp
    change paddedName (dx k) (dy k) (fitsX k a b) (fitsY k a b) (baseStrong k a b).axes.name (e.cells q)=_
    rw [paddedName_apply]
    exact native_name k a b q
  · have hout:=paddedName_outside (dx k) (dy k) (fitsX k a b) (fitsY k a b)
      (baseStrong k a b).axes.name p hp
    change paddedName (dx k) (dy k) (fitsX k a b) (fitsY k a b) (baseStrong k a b).axes.name p=_
    rw [hout]
    have hb : ¬(dx k≤p.1.val ∧p.1.val<dx k+(base k a b).width ∧
        dy k≤p.2.val ∧p.2.val<dy k+(base k a b).height) := by
      intro h
      apply hp
      refine ⟨(⟨p.1.val-dx k,by omega⟩,⟨p.2.val-dy k,by omega⟩),?_⟩
      apply Prod.ext <;> apply Fin.ext
      · change dx k+(p.1.val-dx k)=p.1.val; omega
      · change dy k+(p.2.val-dy k)=p.2.val; omega
    have hx : p.1.val<200005:=p.1.isLt
    have hy : p.2.val<198066:=p.2.isLt
    cases k
    all_goals
      change ¬(_≤p.1.val ∧p.1.val<_ ∧_≤p.2.val ∧p.2.val<_) at hb
      dsimp only [coordinateName]
      first
      | change ¬(0≤p.1.val ∧p.1.val<0+200005 ∧99023≤p.2.val ∧p.2.val<99023+21) at hb
      | change ¬(99992≤p.1.val ∧p.1.val<99992+21 ∧0≤p.2.val ∧p.2.val<0+198066) at hb
      | change ¬(99992≤p.1.val ∧p.1.val<99992+100013 ∧99023≤p.2.val ∧p.2.val<99023+99043) at hb
      | change ¬(0≤p.1.val ∧p.1.val<0+100013 ∧99023≤p.2.val ∧p.2.val<99023+99043) at hb
      | change ¬(99992≤p.1.val ∧p.1.val<99992+100013 ∧0≤p.2.val ∧p.2.val<0+99044) at hb
      | change ¬(0≤p.1.val ∧p.1.val<0+100013 ∧0≤p.2.val ∧p.2.val<0+99044) at hb
    all_goals split_ifs <;> simp_all <;> omega

/-- A seven-cell collar includes all ordinary and full-gate seam overlaps. -/
def InCollar : Face→Cell→Prop
  | .west,p=>p.1.val<7
  | .east,p=>199998≤p.1.val
  | .north,p=>p.2.val<7
  | .south,p=>198059≤p.2.val

def collarName (f : Face) (p : Cell) : AxisTrack :=
  match f with
  | .west | .east=>if p.2.val=99033 then .horizontal 99033 else .outside
  | .north | .south=>if p.1.val=100002 then .vertical 100002 else .outside

private theorem coordinateName_collar (k : Kind) (f : Face) (p : Cell) (hp : InCollar f p) :
    coordinateName k p=if FaceUsed k f then collarName f p else .outside := by
  cases k <;> cases f <;>
    dsimp only [coordinateName,InCollar,FaceUsed,sourceFace,targetFace,collarName] at hp ⊢
  all_goals split_ifs <;> simp_all
  all_goals omega

theorem axisTracks_collar (k : Kind) (a b : Bool) (f : Face) (p : Cell) (hp : InCollar f p) :
    (axisTracks k a b).name p=if FaceUsed k f then collarName f p else .outside := by
  rw [axisTracks_name]
  exact coordinateName_collar k f p hp

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
