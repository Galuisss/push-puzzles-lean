/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalProfileForeign
public import PushFS.Reduction.PhysicalSlotSeparation

/-! Literal empty macrocell side corridors and the short corner seams are free on the whole physical board. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles

open Cslib.Complexity.NCL PhysicalBitmap Gadgets.Wires GateTileRouting FullGateBoundary
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board

private theorem wall_row_support (k : Key) (q : Cell (piece k).width (piece k).height) (south : Bool)
    (hy : pad k+q.2.val=if south then 198062 else 1) (hw : q∈(piece k).board.walls) :
    Used k (if south then .south else .north) ∧100001≤pad k+q.1.val ∧pad k+q.1.val≤100003 := by
  cases k with
  | inl g=>
    cases south
    · have hh:=(FullGateBoundary.walls g .north q (by change q.2.val<7; change 0+q.2.val=1 at hy; omega)).mp hw
      refine ⟨hh.1,?_⟩
      have ht:=hh.2
      change q.1.val=100001 ∨q.1.val=100002 at ht
      change 100001≤0+q.1.val ∧0+q.1.val≤100003
      omega
    · have hh:=(FullGateBoundary.walls g .south q (by change 198061≤q.2.val; change 0+q.2.val=198062 at hy; omega)).mp hw
      refine ⟨hh.1,?_⟩
      have ht:=hh.2
      change q.1.val=100001 ∨q.1.val=100002 at ht
      change 100001≤0+q.1.val ∧0+q.1.val≤100003
      omega
  | inr a=>
    cases south
    · have hh:=(Catalog.boundary_walls a.1 a.2.1 a.2.2 .north q (by change q.2.val<5; change 1+q.2.val=1 at hy; omega)).mp hw
      refine ⟨hh.1,?_⟩
      have ht:=hh.2
      change q.1.val=100000 ∨q.1.val=100001 at ht
      change 100001≤1+q.1.val ∧1+q.1.val≤100003
      omega
    · have hh:=(Catalog.boundary_walls a.1 a.2.1 a.2.2 .south q (by change 198061≤q.2.val; change 1+q.2.val=198062 at hy; omega)).mp hw
      refine ⟨hh.1,?_⟩
      have ht:=hh.2
      change q.1.val=100000 ∨q.1.val=100001 at ht
      change 100001≤1+q.1.val ∧1+q.1.val≤100003
      omega

private theorem wire_row_bounds (k : Catalog.Kind) (a : Bool) (q : Catalog.Cell)
    (hy : q.2.val=0 ∨q.2.val=198061) (hb : Catalog.SlotRegion k a q) : q.1.val=100002 := by
  cases k <;> dsimp only [Catalog.SlotRegion,Catalog.SlotBounds] at hb <;> omega

private theorem mark_row_support (k : Key) (q : Cell (piece k).width (piece k).height) (south goal : Bool)
    (hy : pad k+q.2.val=if south then 198062 else 1) (hq : q∈marks goal k) :
    Used k (if south then .south else .north) ∧100001≤pad k+q.1.val ∧pad k+q.1.val≤100003 := by
  obtain ⟨l,rfl⟩:=mark_slot goal k q hq
  cases k with
  | inl g=>
    cases south
    · obtain ⟨r,prev,hd,he⟩:=gate_slots_frame g goal .north l (by change _<7; change 0+_=1 at hy; omega)
      refine ⟨⟨r,hd⟩,?_⟩
      have hx:=congrArg Prod.fst he
      change _=100003 at hx
      change 100001≤0+_ ∧0+_≤100003
      omega
    · obtain ⟨r,prev,hd,he⟩:=gate_slots_frame g goal .south l (by change 198061≤_; change 0+_=198062 at hy; omega)
      refine ⟨⟨r,hd⟩,?_⟩
      have hx:=congrArg Prod.fst he
      change _=100003 at hx
      change 100001≤0+_ ∧0+_≤100003
      omega
  | inr a=>
    have hb:=wire_slots_bounds a goal l
    have hface : Catalog.InFace (if south then .south else .north) (slots goal (.inr a) l):=by
      cases south
      · change _<5; change 1+_=1 at hy; omega
      · change 198061≤_; change 1+_=198062 at hy; omega
    have hu:=wire_slots_face a goal _ l hface
    refine ⟨by cases south <;>exact hu,?_⟩
    have hx :=wire_row_bounds a.1 (wirePhase a goal) (slots goal (.inr a) l) (by
      cases south
      · change 1+_=1 at hy; omega
      · change 1+_=198062 at hy; omega) hb
    change 100001≤1+_ ∧1+_≤100003
    omega

private theorem wall_col_support (k : Key) (q : Cell (piece k).width (piece k).height) (east : Bool)
    (hx : pad k+q.1.val=if east then 200001 else 1) (hw : q∈(piece k).board.walls) :
    Used k (if east then .east else .west) ∧99034≤pad k+q.2.val ∧pad k+q.2.val≤99036 := by
  cases k with
  | inl g=>
    cases east
    · have hh:=(FullGateBoundary.walls g .west q (by change q.1.val<7; change 0+q.1.val=1 at hx; omega)).mp hw
      refine ⟨hh.1,?_⟩
      have ht:=hh.2
      change q.2.val=99035 ∨q.2.val=99036 at ht
      change 99034≤0+q.2.val ∧0+q.2.val≤99036
      omega
    · have hh:=(FullGateBoundary.walls g .east q (by change 200000≤q.1.val; change 0+q.1.val=200001 at hx; omega)).mp hw
      refine ⟨hh.1,?_⟩
      have ht:=hh.2
      change q.2.val=99035 ∨q.2.val=99036 at ht
      change 99034≤0+q.2.val ∧0+q.2.val≤99036
      omega
  | inr a=>
    cases east
    · have hh:=(Catalog.boundary_walls a.1 a.2.1 a.2.2 .west q (by change q.1.val<5; change 1+q.1.val=1 at hx; omega)).mp hw
      refine ⟨hh.1,?_⟩
      have ht:=hh.2
      change q.2.val=99034 ∨q.2.val=99035 at ht
      change 99034≤1+q.2.val ∧1+q.2.val≤99036
      omega
    · have hh:=(Catalog.boundary_walls a.1 a.2.1 a.2.2 .east q (by change 200000≤q.1.val; change 1+q.1.val=200001 at hx; omega)).mp hw
      refine ⟨hh.1,?_⟩
      have ht:=hh.2
      change q.2.val=99034 ∨q.2.val=99035 at ht
      change 99034≤1+q.2.val ∧1+q.2.val≤99036
      omega

private theorem wire_col_bounds (k : Catalog.Kind) (a : Bool) (q : Catalog.Cell)
    (hx : q.1.val=0 ∨q.1.val=200000) (hb : Catalog.SlotRegion k a q) : q.2.val=99033 := by
  cases k <;> dsimp only [Catalog.SlotRegion,Catalog.SlotBounds] at hb <;> omega

private theorem mark_col_support (k : Key) (q : Cell (piece k).width (piece k).height) (east goal : Bool)
    (hx : pad k+q.1.val=if east then 200001 else 1) (hq : q∈marks goal k) :
    Used k (if east then .east else .west) ∧99034≤pad k+q.2.val ∧pad k+q.2.val≤99036 := by
  obtain ⟨l,rfl⟩:=mark_slot goal k q hq
  cases k with
  | inl g=>
    cases east
    · obtain ⟨r,prev,hd,he⟩:=gate_slots_frame g goal .west l (by change _<7; change 0+_=1 at hx; omega)
      refine ⟨⟨r,hd⟩,?_⟩
      have hcoord:=congrArg Prod.snd he
      change _=99034 at hcoord
      change 99034≤0+_ ∧0+_≤99036
      omega
    · obtain ⟨r,prev,hd,he⟩:=gate_slots_frame g goal .east l (by change 200000≤_; change 0+_=200001 at hx; omega)
      refine ⟨⟨r,hd⟩,?_⟩
      have hcoord:=congrArg Prod.snd he
      change _=99034 at hcoord
      change 99034≤0+_ ∧0+_≤99036
      omega
  | inr a=>
    have hb:=wire_slots_bounds a goal l
    have hface : Catalog.InFace (if east then .east else .west) (slots goal (.inr a) l):=by
      cases east
      · change _<5; change 1+_=1 at hx; omega
      · change 200000≤_; change 1+_=200001 at hx; omega
    have hu:=wire_slots_face a goal _ l hface
    refine ⟨by cases east <;>exact hu,?_⟩
    have hx :=wire_col_bounds a.1 (wirePhase a goal) (slots goal (.inr a) l) (by
      cases east
      · change 1+_=1 at hx; omega
      · change 1+_=200001 at hx; omega) hb
    change 99034≤1+_ ∧1+_≤99036
    omega

private theorem mesh_row_owner (p r : GridRouting.Point) (k : Key)
    (q : Cell (piece k).width (piece k).height)
    (hlo : strideX*p.1+1≤(coordinates r k q).1)
    (hhi : (coordinates r k q).1≤strideX*p.1+200005)
    (hy : (coordinates r k q).2=strideY*p.2+1)
    (support : ∀south : Bool,pad k+q.2.val=(if south then 198062 else 1)→
      Used k (if south then .south else .north) ∧100001≤pad k+q.1.val ∧pad k+q.1.val≤100003) :
    r=p ∨neighbor .south r=some p ∧Used k .south := by
  have hb:=coordinate_bounds r k q
  have hry : r.2=p.2 ∨r.2+1=p.2:=by
    dsimp only [strideX,strideY] at hb hy
    omega
  dsimp only [coordinates,offset,strideX,strideY] at hlo hhi hy
  rcases hry with hry|hry
  · have hh:=support false (by change pad k+q.2.val=1; omega)
    have hrx : r.1=p.1:=by omega
    exact Or.inl (Prod.ext hrx hry)
  · have hh:=support true (by change pad k+q.2.val=198062; omega)
    have hrx : r.1=p.1:=by omega
    refine Or.inr ⟨?_,hh.1⟩
    simp only [neighbor,Option.some.injEq,Prod.ext_iff]
    exact ⟨hrx,hry⟩

private theorem empty_row_obstacle (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (p r : GridRouting.Point) (k : Key)
    (hempty : CellPlan.cell (v,p)=none) (hk : key (CellPlan.cell (v,r))=some k)
    (q : Cell (piece k).width (piece k).height)
    (hlo : strideX*p.1+1≤(coordinates r k q).1)
    (hhi : (coordinates r k q).1≤strideX*p.1+200005)
    (hy : (coordinates r k q).2=strideY*p.2+1)
    (support : ∀south : Bool,pad k+q.2.val=(if south then 198062 else 1)→
      Used k (if south then .south else .north) ∧100001≤pad k+q.1.val ∧pad k+q.1.val≤100003) : False := by
  rcases mesh_row_owner p r k q hlo hhi hy support with hr|⟨hn,hu⟩
  · rw [hr,hempty] at hk
    cases hk
  · have hh:=(CellPlan.used_reciprocal v hP hT hn).mp ((used_key hk .south).mp hu)
    rw [hempty] at hh
    exact hh

private theorem mesh_col_owner (p r : GridRouting.Point) (k : Key)
    (q : Cell (piece k).width (piece k).height)
    (hlo : strideY*p.2+1≤(coordinates r k q).2)
    (hhi : (coordinates r k q).2≤strideY*p.2+198066)
    (hy : (coordinates r k q).1=strideX*p.1+1)
    (support : ∀east : Bool,pad k+q.1.val=(if east then 200001 else 1)→
      Used k (if east then .east else .west) ∧99034≤pad k+q.2.val ∧pad k+q.2.val≤99036) :
    r=p ∨neighbor .east r=some p ∧Used k .east := by
  have hb:=coordinate_bounds r k q
  have hry : r.1=p.1 ∨r.1+1=p.1:=by
    dsimp only [strideY,strideX] at hb hy
    omega
  dsimp only [coordinates,offset,strideY,strideX] at hlo hhi hy
  rcases hry with hry|hry
  · have hh:=support false (by change pad k+q.1.val=1; omega)
    have hrx : r.2=p.2:=by omega
    exact Or.inl (Prod.ext hry hrx)
  · have hh:=support true (by change pad k+q.1.val=200001; omega)
    have hrx : r.2=p.2:=by omega
    refine Or.inr ⟨?_,hh.1⟩
    simp only [neighbor,Option.some.injEq,Prod.ext_iff]
    exact ⟨hry,hrx⟩

private theorem empty_col_obstacle (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (p r : GridRouting.Point) (k : Key)
    (hempty : CellPlan.cell (v,p)=none) (hk : key (CellPlan.cell (v,r))=some k)
    (q : Cell (piece k).width (piece k).height)
    (hlo : strideY*p.2+1≤(coordinates r k q).2)
    (hhi : (coordinates r k q).2≤strideY*p.2+198066)
    (hy : (coordinates r k q).1=strideX*p.1+1)
    (support : ∀east : Bool,pad k+q.1.val=(if east then 200001 else 1)→
      Used k (if east then .east else .west) ∧99034≤pad k+q.2.val ∧pad k+q.2.val≤99036) : False := by
  rcases mesh_col_owner p r k q hlo hhi hy support with hr|⟨hn,hu⟩
  · rw [hr,hempty] at hk
    cases hk
  · have hh:=(CellPlan.used_reciprocal v hP hT hn).mp ((used_key hk .east).mp hu)
    rw [hempty] at hh
    exact hh

private theorem mesh_row_seam_obstacle (p r : GridRouting.Point) (k : Key)
    (q : Cell (piece k).width (piece k).height)
    (hlo : strideX*p.1+200001≤(coordinates r k q).1)
    (hhi : (coordinates r k q).1≤strideX*p.1+200005)
    (hy : (coordinates r k q).2=strideY*p.2+1)
    (support : ∀south : Bool,pad k+q.2.val=(if south then 198062 else 1)→
      Used k (if south then .south else .north) ∧100001≤pad k+q.1.val ∧pad k+q.1.val≤100003) : False := by
  have hb:=coordinate_bounds r k q
  have hry : r.2=p.2 ∨r.2+1=p.2:=by dsimp only [strideX,strideY] at hb hy; omega
  dsimp only [coordinates,offset,strideX,strideY] at hlo hhi hy
  rcases hry with hry|hry
  · have hh:=support false (by change pad k+q.2.val=1; omega)
    omega
  · have hh:=support true (by change pad k+q.2.val=198062; omega)
    omega

private theorem mesh_col_seam_obstacle (p r : GridRouting.Point) (k : Key)
    (q : Cell (piece k).width (piece k).height)
    (hlo : strideY*p.2+198062≤(coordinates r k q).2)
    (hhi : (coordinates r k q).2≤strideY*p.2+198066)
    (hx : (coordinates r k q).1=strideX*p.1+1)
    (support : ∀east : Bool,pad k+q.1.val=(if east then 200001 else 1)→
      Used k (if east then .east else .west) ∧99034≤pad k+q.2.val ∧pad k+q.2.val≤99036) : False := by
  have hb:=coordinate_bounds r k q
  have hrx : r.1=p.1 ∨r.1+1=p.1:=by dsimp only [strideX,strideY] at hb hx; omega
  dsimp only [coordinates,offset,strideX,strideY] at hlo hhi hx
  rcases hrx with hrx|hrx
  · have hh:=support false (by change pad k+q.1.val=1; omega)
    omega
  · have hh:=support true (by change pad k+q.1.val=200001; omega)
    omega

end PushPuzzle.PushFS.Reduction.PhysicalTiles

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory
open Cslib.Complexity.NCL PhysicalBitmap Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

/-- The complete literal top side corridor of every empty source macrocell is free in every actual mixed box inventory. -/
theorem empty_top_free (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : GridRouting.Point)
    (hempty : CellPlan.cell (v,p)=none)
    (q : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hlo : strideX*p.1+1≤q.1.val) (hhi : q.1.val≤strideX*p.1+200005)
    (hy : q.2.val=strideY*p.2+1) :
    Free (atlas v hP hT).board ((atlas v hP hT).profileBoxes f) q := by
  constructor
  · intro hw
    obtain ⟨i,s,hs,he⟩:=(wall_membership v hP hT q).mp hw
    exact PhysicalTiles.empty_row_obstacle v hP hT p (position i) (tile i) hempty (key_eq i) s
      (by simpa only [he] using hlo) (by simpa only [he] using hhi) (by simpa only [he] using hy)
      (fun south h=>PhysicalTiles.wall_row_support (tile i) s south h hs)
  · intro hb
    obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hb
    obtain ⟨s,hs,he⟩:=Finset.mem_map.mp hj
    let i:=(numbering v).symm j
    have hmark : s∈PhysicalTiles.marks (f j) (tile i):=hs
    have hcoords : PhysicalTiles.coordinates (position i) (tile i) s=(q.1.val,q.2.val):=
      congrArg (fun p=>(p.1.val,p.2.val)) he
    exact PhysicalTiles.empty_row_obstacle v hP hT p (position i) (tile i) hempty (key_eq i) s
      (by simpa only [hcoords] using hlo) (by simpa only [hcoords] using hhi) (by simpa only [hcoords] using hy)
      (fun south h=>PhysicalTiles.mark_row_support (tile i) s south (f j) h hmark)

/-- The complete literal left side corridor of every empty source macrocell is free in every actual mixed box inventory. -/
theorem empty_left_free (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : GridRouting.Point)
    (hempty : CellPlan.cell (v,p)=none)
    (q : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hlo : strideY*p.2+1≤q.2.val) (hhi : q.2.val≤strideY*p.2+198066)
    (hy : q.1.val=strideX*p.1+1) :
    Free (atlas v hP hT).board ((atlas v hP hT).profileBoxes f) q := by
  constructor
  · intro hw
    obtain ⟨i,s,hs,he⟩:=(wall_membership v hP hT q).mp hw
    exact PhysicalTiles.empty_col_obstacle v hP hT p (position i) (tile i) hempty (key_eq i) s
      (by simpa only [he] using hlo) (by simpa only [he] using hhi) (by simpa only [he] using hy)
      (fun south h=>PhysicalTiles.wall_col_support (tile i) s south h hs)
  · intro hb
    obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hb
    obtain ⟨s,hs,he⟩:=Finset.mem_map.mp hj
    let i:=(numbering v).symm j
    have hmark : s∈PhysicalTiles.marks (f j) (tile i):=hs
    have hcoords : PhysicalTiles.coordinates (position i) (tile i) s=(q.1.val,q.2.val):=
      congrArg (fun p=>(p.1.val,p.2.val)) he
    exact PhysicalTiles.empty_col_obstacle v hP hT p (position i) (tile i) hempty (key_eq i) s
      (by simpa only [hcoords] using hlo) (by simpa only [hcoords] using hhi) (by simpa only [hcoords] using hy)
      (fun south h=>PhysicalTiles.mark_col_support (tile i) s south (f j) h hmark)

/-- The literal four-step east corner bridge is free in every actual mixed box inventory. -/
theorem east_bridge_free (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : GridRouting.Point)
    (q : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hlo : strideX*p.1+200001≤q.1.val) (hhi : q.1.val≤strideX*p.1+200005)
    (hy : q.2.val=strideY*p.2+1) :
    Free (atlas v hP hT).board ((atlas v hP hT).profileBoxes f) q := by
  constructor
  · intro hw
    obtain ⟨i,s,hs,he⟩:=(wall_membership v hP hT q).mp hw
    exact PhysicalTiles.mesh_row_seam_obstacle p (position i) (tile i) s
      (by simpa only [he] using hlo) (by simpa only [he] using hhi) (by simpa only [he] using hy)
      (fun south h=>PhysicalTiles.wall_row_support (tile i) s south h hs)
  · intro hb
    obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hb
    obtain ⟨s,hs,he⟩:=Finset.mem_map.mp hj
    let i:=(numbering v).symm j
    have hmark : s∈PhysicalTiles.marks (f j) (tile i):=hs
    have hcoords : PhysicalTiles.coordinates (position i) (tile i) s=(q.1.val,q.2.val):=
      congrArg (fun p=>(p.1.val,p.2.val)) he
    exact PhysicalTiles.mesh_row_seam_obstacle p (position i) (tile i) s
      (by simpa only [hcoords] using hlo) (by simpa only [hcoords] using hhi) (by simpa only [hcoords] using hy)
      (fun south h=>PhysicalTiles.mark_row_support (tile i) s south (f j) h hmark)

/-- The literal four-step south corner bridge is free in every actual mixed box inventory. -/
theorem south_bridge_free (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : GridRouting.Point)
    (q : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hlo : strideY*p.2+198062≤q.2.val) (hhi : q.2.val≤strideY*p.2+198066)
    (hy : q.1.val=strideX*p.1+1) :
    Free (atlas v hP hT).board ((atlas v hP hT).profileBoxes f) q := by
  constructor
  · intro hw
    obtain ⟨i,s,hs,he⟩:=(wall_membership v hP hT q).mp hw
    exact PhysicalTiles.mesh_col_seam_obstacle p (position i) (tile i) s
      (by simpa only [he] using hlo) (by simpa only [he] using hhi) (by simpa only [he] using hy)
      (fun south h=>PhysicalTiles.wall_col_support (tile i) s south h hs)
  · intro hb
    obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hb
    obtain ⟨s,hs,he⟩:=Finset.mem_map.mp hj
    let i:=(numbering v).symm j
    have hmark : s∈PhysicalTiles.marks (f j) (tile i):=hs
    have hcoords : PhysicalTiles.coordinates (position i) (tile i) s=(q.1.val,q.2.val):=
      congrArg (fun p=>(p.1.val,p.2.val)) he
    exact PhysicalTiles.mesh_col_seam_obstacle p (position i) (tile i) s
      (by simpa only [hcoords] using hlo) (by simpa only [hcoords] using hhi) (by simpa only [hcoords] using hy)
      (fun south h=>PhysicalTiles.mark_col_support (tile i) s south (f j) h hmark)

end PushPuzzle.PushFS.Reduction.PhysicalInventory
