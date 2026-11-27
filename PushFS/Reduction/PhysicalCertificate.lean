/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalInterior
public import PushFS.Reduction.PhysicalGoalSeparation
public import PushFS.Reduction.FullGateStatics.Certificate

/-! C1–C3 for the entire actual physical board emitted by a checked source word. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL PhysicalBitmap Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

private theorem source_mem (k : PhysicalTiles.Key) (l : PhysicalTiles.Labels k) :
    (PhysicalTiles.matching k).source l∈(PhysicalTiles.piece k).initial.boxes := by
  rw [←(PhysicalTiles.matching k).source_image]
  exact Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩

private theorem target_mem (k : PhysicalTiles.Key) (l : PhysicalTiles.Labels k) :
    (PhysicalTiles.matching k).target l∈(PhysicalTiles.piece k).board.goals := by
  rw [←(PhysicalTiles.matching k).target_image]
  exact Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩

private theorem target_active (k : PhysicalTiles.Key) (l : PhysicalTiles.Labels k) :
    (PhysicalTiles.classifier k).name ((PhysicalTiles.matching k).target l)≠.outside := by
  have hc:=GateTileRouting.FullGateStatics.component_name (PhysicalTiles.classifier k)
    (component_eq_iff.mpr ((PhysicalTiles.matching k).connected l))
  exact hc ▸PhysicalTiles.initial_active k _ (source_mem k l)

private theorem wire_sparse (a : Catalog.Bitmap.Args)
    (p : Catalog.Cell) (hp : p∈(Catalog.puzzle a.1 a.2.1 a.2.2).board.goals)
    (q : Catalog.Cell) (hq : q∈(Catalog.puzzle a.1 a.2.1 a.2.2).board.goals) (d : Direction) : ¬Adjacent d p q := by
  let e:=GridEmbedding.translate (Catalog.dx a.1) (Catalog.dy a.1)
    (Catalog.fitsX a.1 a.2.1 a.2.2) (Catalog.fitsY a.1 a.2.1 a.2.2)
  have he:=Catalog.placed_goals (Catalog.baseMatching a.1 a.2.1 a.2.2) (Catalog.dx a.1) (Catalog.dy a.1)
    (Catalog.fitsX a.1 a.2.1 a.2.2) (Catalog.fitsY a.1 a.2.1 a.2.2)
  have hp' : p∈(Catalog.base a.1 a.2.1 a.2.2).board.goals.map e.cells:=he ▸hp
  have hq' : q∈(Catalog.base a.1 a.2.1 a.2.2).board.goals.map e.cells:=he ▸hq
  obtain ⟨p,hpu,rfl⟩:=Finset.mem_map.mp hp'
  obtain ⟨q,hqv,rfl⟩:=Finset.mem_map.mp hq'
  exact fun ha=>(Catalog.baseStrong a.1 a.2.1 a.2.2).sparse p hpu q hqv d
    ((Polyline.translate_adjacent_iff _ _ _ _ d p q).mp ha)

private theorem raw_owner (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i j : Index v) (l : PhysicalTiles.Labels (tile i)) (k : PhysicalTiles.Labels (tile j)) (d : Direction)
    (ha : Adjacent d (rawTarget v ⟨i,l⟩) (rawTarget v ⟨j,k⟩)) : i=j := by
  exact position_injective (PhysicalTiles.slot_near_owners v hP hT true (key_eq i) (key_eq j) l k
    (Adjacent.nearby ha))

private theorem same_macro_separated (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Index v) (l k : PhysicalTiles.Labels (tile i))
    (he : (axisClassifier v hP hT).name (rawTarget v ⟨i,l⟩)=
      (axisClassifier v hP hT).name (rawTarget v ⟨i,k⟩)) (d : Direction) :
    ¬Adjacent d (rawTarget v ⟨i,l⟩) (rawTarget v ⟨i,k⟩) := by
  intro ha
  rcases i with ⟨⟨r,t⟩,hi⟩
  cases t with
  | inl g=>
    let i : Index v:=⟨(r,.inl g),hi⟩
    let p:=(PhysicalTiles.matching (.inl g)).target l
    let q:=(PhysicalTiles.matching (.inl g)).target k
    have hp:=target_mem (.inl g) l
    have hq:=target_mem (.inl g) k
    change Adjacent d ((axisChart v i).embedding.cells p) ((axisChart v i).embedding.cells q) at ha
    have hal:=(Polyline.translate_adjacent_iff _ _ _ _ d p q).mp ha
    obtain ⟨⟨a,x⟩,hpa⟩:=(GateTileRouting.full_goals_mem g p).mp hp
    obtain ⟨⟨b,y⟩,hqb⟩:=(GateTileRouting.full_goals_mem g q).mp hq
    have hab : Adjacent d (GateTileRouting.rawTarget g ⟨a,x⟩) (GateTileRouting.rawTarget g ⟨b,y⟩) :=
      hpa.symm ▸hqb.symm ▸hal
    obtain ⟨ha0,hb0⟩:=GateTileRouting.FullGateStatics.adjacent_targets_core g a b x y d hab
    subst a
    subst b
    have hpi : PhysicalTiles.Inner (.inl g) p := by
      rw [←hpa]
      simpa only [PhysicalTiles.Inner,PhysicalTiles.pad,Nat.zero_add,strideX,strideY] using
        GateTileRouting.FullGateStatics.core_target_bounds g x
    have hqi : PhysicalTiles.Inner (.inl g) q := by
      rw [←hqb]
      simpa only [PhysicalTiles.Inner,PhysicalTiles.pad,Nat.zero_add,strideX,strideY] using
        GateTileRouting.FullGateStatics.core_target_bounds g y
    have hpn:=inner_name v hP hT i p hpi (target_active (.inl g) l)
    have hqn:=inner_name v hP hT i q hqi (target_active (.inl g) k)
    change (axisClassifier v hP hT).name ((axisChart v i).embedding.cells p)=
      (axisClassifier v hP hT).name ((axisChart v i).embedding.cells q) at he
    have hn:=AxisTrack.shift_injective (axisChart v i).dx (axisChart v i).dy
      (hpn.symm.trans (he.trans hqn))
    exact GateTileRouting.FullGateStatics.named_separated g p hp q hq hn d hal
  | inr a=>
    have hal:=(Polyline.translate_adjacent_iff _ _ _ _ d
      ((PhysicalTiles.matching (.inr a)).target l) ((PhysicalTiles.matching (.inr a)).target k)).mp ha
    exact wire_sparse a _ (target_mem (.inr a) l) _ (target_mem (.inr a) k) d hal

private theorem raw_targets_separated (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (i j : Index v) (l : PhysicalTiles.Labels (tile i)) (k : PhysicalTiles.Labels (tile j))
    (he : (axisClassifier v hP hT).name (rawTarget v ⟨i,l⟩)=
      (axisClassifier v hP hT).name (rawTarget v ⟨j,k⟩)) (d : Direction) :
    ¬Adjacent d (rawTarget v ⟨i,l⟩) (rawTarget v ⟨j,k⟩) := by
  intro ha
  have hij:=raw_owner v hP hT i j l k d ha
  subst j
  exact same_macro_separated v hP hT i l k he d ha

theorem goals_named_separated (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (p : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hp : p∈(puzzle v hP hT).board.goals)
    (q : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hq : q∈(puzzle v hP hT).board.goals)
    (he : (axisClassifier v hP hT).name p=(axisClassifier v hP hT).name q) (d : Direction) : ¬Adjacent d p q := by
  rw [←(rawSlotMatching v hP hT).target_image] at hp hq
  obtain ⟨⟨i,l⟩,_,hp⟩:=Finset.mem_map.mp hp
  obtain ⟨⟨j,k⟩,_,hq⟩:=Finset.mem_map.mp hq
  have hpi:=(raw_target v hP hT i l).symm.trans hp
  have hqj:=(raw_target v hP hT j k).symm.trans hq
  have hn:=(congrArg (axisClassifier v hP hT).name hpi).trans
    (he.trans (congrArg (axisClassifier v hP hT).name hqj).symm)
  intro ha
  exact raw_targets_separated v hP hT i j l k hn d (hpi.symm ▸hqj.symm ▸ha)

noncomputable def axisTracks (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) :
    AxisTracks (puzzle v hP hT) where
  name:=(axisClassifier v hP hT).name
  supported:=(axisClassifier v hP hT).supported
  active:=axis_initial_active v hP hT
  displacement:=(axisClassifier v hP hT).displacement
  separated:=goals_named_separated v hP hT

/-- Every complete actual physical source instance satisfies the SCC transfer certificate. -/
theorem certificate (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) :
    Certificate (puzzle v hP hT) :=
  (axisTracks v hP hT).toStaticTracks.certificate (rawSlotMatching v hP hT)

end PushPuzzle.PushFS.Reduction.PhysicalInventory
