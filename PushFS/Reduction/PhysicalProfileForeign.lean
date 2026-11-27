/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalMarkedInventory
public import PushFS.Reduction.PhysicalPlacements
public import PushFS.Reduction.StorageReplay

/-! Actual mixed-profile foreign boxes retain their complete source-cell owners, selected phases and literal coordinates. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles


theorem mark_slot (goal : Bool) (k : Key) (p : Cell (piece k).width (piece k).height)
    (hp : p∈marks goal k) : ∃l : Labels k,slots goal k l=p := by
  cases goal
  · change p∈(piece k).initial.boxes at hp
    rw [←(matching k).source_image] at hp
    obtain ⟨l,_,he⟩:=Finset.mem_map.mp hp
    exact ⟨l,he⟩
  · change p∈(piece k).board.goals at hp
    rw [←(matching k).target_image] at hp
    obtain ⟨l,_,he⟩:=Finset.mem_map.mp hp
    exact ⟨l,he⟩
end PushPuzzle.PushFS.Reduction.PhysicalTiles

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory
open Cslib.Complexity.NCL PhysicalBitmap
set_option maxRecDepth 65536
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

theorem profile_foreign (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (i : Index v)
    (p : Cell (PhysicalTiles.piece (tile i)).width (PhysicalTiles.piece (tile i)).height)
    (hp : (embedding v i).cells p∈
      (atlas v hP hT).profileOutside f (numbering v i)) :
    ∃j : Index v,j≠i ∧∃q : Cell (PhysicalTiles.piece (tile j)).width (PhysicalTiles.piece (tile j)).height,
      q∈PhysicalTiles.marks (f (numbering v j)) (tile j) ∧
      PhysicalTiles.coordinates (position i) (tile i) p=PhysicalTiles.coordinates (position j) (tile j) q := by
  obtain ⟨j,hji,hj⟩:=((atlas v hP hT).mem_profileOutside_map f (numbering v i) _).mp hp
  obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hj
  refine ⟨(numbering v).symm j,fun h=>hji ?_,q,?_,?_⟩
  · exact ((numbering v).apply_symm_apply j).symm.trans (congrArg (numbering v) h)
  · change q∈PhysicalTiles.marks (f j) (tile ((numbering v).symm j)) at hq
    rw [(numbering v).apply_symm_apply j]
    exact hq
  · have hxy:=congrArg (fun q=>(q.1.val,q.2.val)) he
    change PhysicalTiles.coordinates (position ((numbering v).symm j)) (tile ((numbering v).symm j)) q=
      PhysicalTiles.coordinates (position i) (tile i) p at hxy
    exact hxy.symm
end PushPuzzle.PushFS.Reduction.PhysicalInventory
