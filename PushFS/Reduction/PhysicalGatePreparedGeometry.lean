/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalGateForeignGeometry
public import PushFS.Reduction.FullGateLineMacros

/-! A released actual neighboring wire leaves the strict single far cell of the full gate's changing arm. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets.Wires GateTileRouting FullGateBoundary
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board

theorem wire_first_sparse (a : Catalog.Bitmap.Args) (goal : Bool) (l : Labels (.inr a)) (d : Direction) :
    ¬Adjacent d (Catalog.firstPoint a.1 (wirePhase a goal)) (slots goal (.inr a) l) := by
  cases goal
  · change ¬Adjacent d (Catalog.firstPoint a.1 a.2.1) ((Catalog.slotMatching a.1 a.2.1 a.2.2).source l)
    rw [←Catalog.source_first a.1 a.2.1 a.2.2]
    exact Catalog.source_sparse a.1 a.2.1 a.2.2 _ l d
  · change ¬Adjacent d (Catalog.firstPoint a.1 a.2.2) ((Catalog.slotMatching a.1 a.2.1 a.2.2).target l)
    rw [←Catalog.target_first a.1 a.2.1 a.2.2]
    exact Catalog.target_sparse a.1 a.2.1 a.2.2 _ l d

theorem wire_last_sparse (a : Catalog.Bitmap.Args) (goal : Bool) (l : Labels (.inr a)) (d : Direction) :
    ¬Adjacent d (slots goal (.inr a) l) (Catalog.lastPoint a.1 (wirePhase a goal)) := by
  cases goal
  · change ¬Adjacent d ((Catalog.slotMatching a.1 a.2.1 a.2.2).source l) (Catalog.lastPoint a.1 a.2.1)
    rw [←Catalog.source_last a.1 a.2.1 a.2.2]
    exact Catalog.source_sparse a.1 a.2.1 a.2.2 l _ d
  · change ¬Adjacent d ((Catalog.slotMatching a.1 a.2.1 a.2.2).target l) (Catalog.lastPoint a.1 a.2.2)
    rw [←Catalog.target_last a.1 a.2.1 a.2.2]
    exact Catalog.target_sparse a.1 a.2.1 a.2.2 l _ d

private theorem released_neighbor_point (d : Direction) (inc a : Bool) (k : Catalog.Kind)
    (p r : ℕ×ℕ) (q : GateTileRouting.C) (s : Catalog.Cell) (hk : Catalog.Straight k)
    (hn : neighbor d p=some r) (hs : Catalog.SlotRegion k a s)
    (hflow : if inc then Catalog.targetDirection k=d.opposite else Catalog.sourceDirection k=d)
    (hphase : a=!inc)
    (he : (strideX*p.1+q.1.val,strideY*p.2+q.2.val)=(strideX*r.1+1+s.1.val,strideY*r.2+1+s.2.val))
    (hfirst : ∀e,¬Adjacent e (Catalog.firstPoint k a) s)
    (hlast : ∀e,¬Adjacent e s (Catalog.lastPoint k a)) :
    (q.1.val,q.2.val)=farEndpoint d inc 1 ∨inc=false ∧(q.1.val,q.2.val)=paddingPoint d := by
  have hfe:=hfirst .east
  have hfw:=hfirst .west
  have hfn:=hfirst .north
  have hfs:=hfirst .south
  have hle:=hlast .east
  have hlw:=hlast .west
  have hln:=hlast .north
  have hls:=hlast .south
  have hqx:=q.1.isLt
  have hqy:=q.2.isLt
  have hx:=congrArg Prod.fst he
  have hy:=congrArg Prod.snd he
  rcases hk with rfl|rfl|rfl
  all_goals cases d <;> cases inc <;> cases a
  all_goals simp only [Catalog.sourceDirection,Catalog.targetDirection,Direction.opposite,
    Bool.false_eq_true,ite_true,ite_false,Bool.not_false,Bool.not_true,reduceCtorEq] at hflow hphase
  all_goals simp only [Catalog.SlotRegion,Catalog.SlotBounds,Catalog.firstPoint,Catalog.lastPoint,
    Bool.toNat_false,Bool.toNat_true,Adjacent,Fin.ext_iff,Catalog.width,Catalog.height] at hs hfe hfw hfn hfs hle hlw hln hls
  all_goals dsimp only [neighbor] at hn
  all_goals try split_ifs at hn
  all_goals simp only [Option.some.injEq,Prod.ext_iff] at hn
  all_goals simp only [farEndpoint,paddingPoint,Bool.toNat_false,Bool.toNat_true,Prod.mk.injEq] at hx hy ⊢
  all_goals dsimp only [strideX,strideY] at hx hy
  all_goals simp_all [Catalog.width,Catalog.height]
  all_goals omega

/-- The released source/target phase has exactly its strict boundary box, with any second source box beyond the last-line rectangle. -/
private theorem gate_released_neighbor_point (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    {p r : GridRouting.Point} {g : GateTileState} {a : Catalog.Bitmap.Args}
    (hg : key (CellPlan.cell (v,p))=some (.inl g)) (ha : key (CellPlan.cell (v,r))=some (.inr a))
    (role : Fin 3) (hn : neighbor (PortAnnulus.outerDirection (g.key role).2) p=some r)
    (goal : Bool) (l : Labels (.inr a)) (q : GateTileRouting.C)
    (hphase : wirePhase a goal=!(g.incoming.get role))
    (he : coordinates p (.inl g) q=coordinates r (.inr a) (slots goal (.inr a) l)) :
    (q.1.val,q.2.val)=farEndpoint (PortAnnulus.outerDirection (g.key role).2) (g.incoming.get role) 1 ∨
      g.incoming.get role=false ∧(q.1.val,q.2.val)=paddingPoint (PortAnnulus.outerDirection (g.key role).2) := by
  exact released_neighbor_point _ _ _ a.1 p r q _ (gate_neighbor_straight v hP hT hn hg ha) hn
    (wire_slots_bounds a goal l) (gate_neighbor_flow v hP hT hg ha role rfl hn) hphase he
    (wire_first_sparse a goal l) (wire_last_sparse a goal l)

private theorem released_point_frame (d : Direction) (inc : Bool) (q : GateTileRouting.C)
    (hq : (q.1.val,q.2.val)=farEndpoint d inc 1 ∨inc=false ∧(q.1.val,q.2.val)=paddingPoint d) :
    InFrame d (q.1.val,q.2.val) := by
  cases d <;> cases inc <;> simp only [farEndpoint,paddingPoint,InFrame,Bool.toNat_false,Bool.toNat_true,Prod.mk.injEq] at hq ⊢ <;> omega

private theorem normal_released_collar (n : ℕ) (d : Direction) (inc : Bool) (dx dy : ℕ)
    (hd : EndPlacement d inc n dx dy) (q : Chain.C n)
    (hq : (lineOrientation d false).coordinates (n+5) 21 dx dy q=farEndpoint d inc 1 ∨
      inc=false ∧(lineOrientation d false).coordinates (n+5) 21 dx dy q=paddingPoint d) :
    q.2.val=10 ∧q.1.val=n+3 := by
  have hx:=q.1.isLt
  have hy:=q.2.isLt
  simp only [RectOrientation.coordinates_point] at hq
  cases d <;> cases inc
  all_goals simp_all [EndPlacement,lineOrientation,RectOrientation.point,RectOrientation.width,RectOrientation.height,
    farEndpoint,paddingPoint]
  all_goals omega

private theorem line_released_collar (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (d : Direction) (inc : Bool) (dx dy : ℕ) (hflip : flip=false) (hd : EndPlacement d inc n dx dy)
    (q : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height)
    (hq : (lineOrientation d flip).coordinates _ _ dx dy q=farEndpoint d inc 1 ∨
      inc=false ∧(lineOrientation d flip).coordinates _ _ dx dy q=paddingPoint d) :
    q∈lineNeighbors flip n hn a b := by
  subst flip
  have hh:=normal_released_collar n d inc dx dy hd q hq
  exact (lineNeighbors_iff false n hn a b q).mpr ⟨hh.1,Or.inr hh.2⟩

/-- A released real wire contributes only the strict far singleton to every line of the corresponding complete arm. -/
theorem gate_released_line_collar (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    {p r : GridRouting.Point} {g : GateTileState} {a : Catalog.Bitmap.Args}
    (hg : key (CellPlan.cell (v,p))=some (.inl g)) (ha : key (CellPlan.cell (v,r))=some (.inr a))
    (role : Fin 3) (hn : neighbor (PortAnnulus.outerDirection (g.key role).2) p=some r)
    (goal : Bool) (l : Labels (.inr a)) (j : Fin (curve (GateTileRouting.key g role)).length)
    (q : Cell (lineInput g role j).width (lineInput g role j).height)
    (hphase : wirePhase a goal=!(g.incoming.get role))
    (he : coordinates p (.inl g) ((lineEmbedding g role j).cells q)=coordinates r (.inr a) (slots goal (.inr a) l)) :
    q∈lineNeighbors (fillerFlip (GateTileRouting.key g role) j.val) (fillerSpan (GateTileRouting.key g role) j.val)
      (filler_shape _ _ j.isLt).2.1 (Inventory.initialPhase g role) (Inventory.targetPhase g role) := by
  let d:=PortAnnulus.outerDirection (g.key role).2
  have hpoint:=gate_released_neighbor_point v hP hT hg ha role hn goal l _ hphase he
  have hf:=released_point_frame d _ _ hpoint
  have ho:=raw_owner g (lineIndex g role j) d
    ((lineRawIso (GateTileRouting.key g role) j.val j.isLt (Inventory.initialPhase g role) (Inventory.targetPhase g role)).cells q) hf
  obtain ⟨hj,_⟩:=ho
  obtain ⟨hflip,htravel,hd⟩:=last_line_metadata (GateTileRouting.key g role) j hj
  have hc:=line_coordinates g role j q
  have hor:=congrArg (fun d : Direction=>(lineOrientation d (fillerFlip (GateTileRouting.key g role) j.val)).coordinates _ _
    (lineOffset (GateTileRouting.key g role) j.val).1 (lineOffset (GateTileRouting.key g role) j.val).2 q) htravel
  have hcoords:=hc.trans hor
  have hp : (lineOrientation d (fillerFlip (GateTileRouting.key g role) j.val)).coordinates _ _
      (lineOffset (GateTileRouting.key g role) j.val).1 (lineOffset (GateTileRouting.key g role) j.val).2 q=farEndpoint d (g.incoming.get role) 1 ∨
      g.incoming.get role=false ∧(lineOrientation d (fillerFlip (GateTileRouting.key g role) j.val)).coordinates _ _
        (lineOffset (GateTileRouting.key g role) j.val).1 (lineOffset (GateTileRouting.key g role) j.val).2 q=paddingPoint d:=
    hcoords ▸hpoint
  exact line_released_collar _ _ (filler_shape _ _ j.isLt).2.1 _ _ d _ _ _ hflip hd q hp

end PushPuzzle.PushFS.Reduction.PhysicalTiles
