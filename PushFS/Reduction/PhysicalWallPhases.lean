/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalCanonical
public import PushFS.Reduction.PhysicalPlacements
public import PushFS.Reduction.FullGateStatics.PhaseWalls
public import PushFS.Gadgets.Wires.Catalog.PhaseWalls

/-! All actual source orientation assignments use one fixed physical wall board. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


namespace PhysicalTiles

open Plan Gadgets.Wires
set_option maxRecDepth 65536

def WallAt (k : Key) (offset p : ℕ×ℕ) : Prop :=
  ∃q : Cell (piece k).width (piece k).height,q∈(piece k).board.walls ∧
    (offset.1+q.1.val,offset.2+q.2.val)=p

private theorem rephase_wallAt (c : Payload) (a b : List Bool) (offset p : ℕ×ℕ) :
    WallAt (rephase c a b) offset p ↔WallAt (payloadKey c) offset p := by
  rcases c with ⟨v,g⟩|⟨e,k,s,t⟩
  · let g' : GateTileState := {g with core:={g.core with initial:=gateSignals (v.ports,a),target:=gateSignals (v.ports,b)}}
    have hw := GateTileRouting.FullGateStatics.full_walls_eq g' g rfl
    change (∃q : GateTileRouting.C,q∈(GateTileRouting.fullPuzzle g').board.walls ∧
      (offset.1+q.1.val,offset.2+q.2.val)=p)↔
        (∃q : GateTileRouting.C,q∈(GateTileRouting.fullPuzzle g).board.walls ∧(offset.1+q.1.val,offset.2+q.2.val)=p)
    exact exists_congr fun q=>and_congr (Eq.to_iff (congrArg (fun xs : Finset GateTileRouting.C=>q∈xs) hw)) Iff.rfl
  · have hw := Catalog.puzzle_walls_eq k (!(a.getD e false)) (!(b.getD e false)) s t
    change (∃q : Catalog.Cell,q∈(Catalog.puzzle k (!(a.getD e false)) (!(b.getD e false))).board.walls ∧
      (offset.1+q.1.val,offset.2+q.2.val)=p)↔
        (∃q : Catalog.Cell,q∈(Catalog.puzzle k s t).board.walls ∧(offset.1+q.1.val,offset.2+q.2.val)=p)
    exact exists_congr fun q=>and_congr (Eq.to_iff (congrArg (fun xs : Finset Catalog.Cell=>q∈xs) hw)) Iff.rfl

end PhysicalTiles

namespace PhysicalInventory

open Cslib.Complexity.NCL PhysicalBitmap
set_option maxRecDepth 65536
attribute [local irreducible] Raster.width Raster.height

def payload (v : CellPlan.Source) (i : Index v) : PhysicalTiles.Payload :=
  (CellPlan.cell (v,position (v := v) i)).getD (.inr (0,(.east,false,false)))

theorem payload_eq (v : CellPlan.Source) (i : Index v) : CellPlan.cell (v,position (v := v) i)=some (payload v i) := by
  cases hc : CellPlan.cell (v,position (v := v) i) with
  | none => exact (PhysicalTiles.key_nonempty (key_eq (v := v) i) hc).elim
  | some c => simp only [payload,hc,Option.getD_some]

theorem payload_key (v : CellPlan.Source) (i : Index v) : PhysicalTiles.payloadKey (payload v i)=tile (v := v) i := by
  have hh := congrArg PhysicalTiles.key (payload_eq v i)
  rw [PhysicalTiles.key_some] at hh
  exact Option.some.inj (hh.symm.trans (key_eq (v := v) i))

def rephaseIndex (v : CellPlan.Source) (a b : List Bool) (i : Index v) : Index (v.1,(a,b)) :=
  ⟨(i.val.1,PhysicalTiles.rephase (payload v i) a b),by
    have hh := congrArg (fun c=>PhysicalTiles.key (PhysicalTiles.rephaseCode c a b)) (payload_eq v i)
    rw [PhysicalTiles.rephase_cell,PhysicalTiles.key_rephaseCode_some] at hh
    exact hh⟩

theorem rephaseIndex_offset (v : CellPlan.Source) (a b : List Bool) (i : Index v) :
    PhysicalTiles.offset (position (v := (v.1,(a,b))) (rephaseIndex v a b i)) (tile (v := (v.1,(a,b))) (rephaseIndex v a b i))=
      PhysicalTiles.offset (position (v := v) i) (tile (v := v) i) := by
  change PhysicalTiles.offset (position (v := v) i) (PhysicalTiles.rephase (payload v i) a b)=_
  unfold PhysicalTiles.offset
  rw [PhysicalTiles.rephase_pad (payload v i) a b,payload_key v i]

private theorem walls_subset (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped
    [] []) (a b : List Bool)
    (p : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hp : p∈(atlas v hP hT).walls) : p∈(atlas (v.1,(a,b)) hP hT).walls := by
  rw [StorageAtlas.walls,Finset.mem_biUnion] at hp
  obtain ⟨j,hj⟩ := hp
  obtain ⟨q,hq,hposition⟩ := Finset.mem_map.mp hj.2
  let i : Index v := (numbering v).symm j
  have he : PhysicalTiles.coordinates (position (v := v) i) (tile (v := v) i) q=(p.1.val,p.2.val) :=
    congrArg (fun p : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)=>(p.1.val,p.2.val)) hposition
  have hi : PhysicalTiles.WallAt (PhysicalTiles.payloadKey (payload v i))
      (PhysicalTiles.offset (position (v := v) i) (tile (v := v) i)) (p.1.val,p.2.val) := by
    rw [payload_key v i]
    exact ⟨q,hq,he⟩
  have hj := (PhysicalTiles.rephase_wallAt (payload v i) a b
    (PhysicalTiles.offset (position (v := v) i) (tile (v := v) i)) (p.1.val,p.2.val)).mpr hi
  have hm' := wall_membership (v.1,(a,b)) hP hT p
  change p∈(atlas (v.1,(a,b)) hP hT).walls ↔_ at hm'
  apply hm'.mpr
  refine ⟨rephaseIndex v a b i,?_⟩
  change PhysicalTiles.WallAt (tile (v := (v.1,(a,b))) (rephaseIndex v a b i))
    (PhysicalTiles.offset (position (v := (v.1,(a,b))) (rephaseIndex v a b i)) (tile (v := (v.1,(a,b))) (rephaseIndex v a b i))) (p.1.val,p.2.val)
  rw [rephaseIndex_offset v a b i]
  exact hj

theorem walls_eq (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) (a b : List Bool) :
    (atlas v hP hT).walls=(atlas (v.1,(a,b)) hP hT).walls := by
  ext p
  exact ⟨walls_subset v hP hT a b p,walls_subset (v.1,(a,b)) hP hT v.2.1 v.2.2 p⟩

end PhysicalInventory
end PushPuzzle.PushFS.Reduction
