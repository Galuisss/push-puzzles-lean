/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalMeshSteps
public import PushFS.Reduction.PhysicalGateWalking
public import PushFS.Reduction.PhysicalWireWalking

/-! Actual player access from the exterior origin to every complete physical tile in every mixed inventory. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board
  StorageAtlas.profileOutside StorageAtlas.profileBoxes PhysicalTiles.marks

private noncomputable def tileHub (v : CellPlan.Source) (i : Index v) :
    Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7) :=
  (embedding v i).cells (PhysicalTiles.piece (tile i)).initial.player

private theorem atlas_player {n w h : ℕ} {L : Fin n→Type} [∀i,Fintype (L i)]
    (A : StorageAtlas n w h L) : A.initial.player=A.player := by
  unfold StorageAtlas.initial
  rfl

private theorem cell_access (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : Raster.Cell v.1) :
    CellPlan.cell (v,(p.1.val,p.2.val))=none ∨
      ∃i : Index v,position i=(p.1.val,p.2.val) ∧∀c : Fin 4,
        Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f (tileHub v i))
          ((atlas v hP hT).profileAt f (macroCorner v.1 p c)) ∧
        Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f (macroCorner v.1 p c))
          ((atlas v hP hT).profileAt f (tileHub v i)) := by
  cases hv : Raster.vertexAt (v.1,(p.1.val,p.2.val)) with
  | some g=>
    obtain ⟨hg,hpos⟩:=Raster.vertexAt_sound hv
    let i:=gateIndex v g hg
    have hp : i.val.1=p := by
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg Prod.fst hpos
      · exact congrArg Prod.snd hpos
    have hc (c : Fin 4) : (gateEmbedding v g hg).cells (GateTileRouting.outerCorner c)=macroCorner v.1 p c :=
      (embedding_corner v i c).trans (congrArg (fun q=>macroCorner v.1 q c) hp)
    have hh : tileHub v i=(gateEmbedding v g hg).cells (GateTileRouting.fullAtlas (gateTileState (g,v.2))).player :=
      congrArg (gateEmbedding v g hg).cells (atlas_player (GateTileRouting.fullAtlas (gateTileState (g,v.2))))
    refine Or.inr ⟨i,hpos,?_⟩
    intro c
    have hr:=gate_profile_corners v hP hT f g hg c
    rw [hc c,←hh] at hr
    exact hr
  | none=>
    cases he : Raster.owner (v.1,(p.1.val,p.2.val)) with
    | none=>exact Or.inl (CellPlan.cell_empty v _ hv he)
    | some e=>
      obtain ⟨k,hk⟩:=CellPlan.cell_wire v hP hT _ hv he
      let a : Catalog.Bitmap.Args:=(k,!(v.2.1.getD e false),!(v.2.2.getD e false))
      have ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a) := by
        rw [hk]
        rfl
      refine Or.inr ⟨wireIndex v p a ha,rfl,?_⟩
      intro c
      exact wire_profile_corners v hP hT f p a ha c

private theorem empty_sides (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : Raster.Cell v.1)
    (he : CellPlan.cell (v,(p.1.val,p.2.val))=none) (c : Fin 4) (hc : c=1 ∨c=2) :
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f (meshPoint v.1 p))
      ((atlas v hP hT).profileAt f (macroCorner v.1 p c)) ∧
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f (macroCorner v.1 p c))
      ((atlas v hP hT).profileAt f (meshPoint v.1 p)) := by
  rcases hc with rfl|rfl
  · exact empty_top_walk v hP hT f (p.1.val,p.2.val) he _ _
      (by norm_num [meshPoint,macroCorner,cornerX,cornerY,strideX,strideY,Nat.mul_add])
      (by norm_num [macroCorner,cornerX,cornerY,strideX,strideY,Nat.mul_add])
  · exact empty_left_walk v hP hT f (p.1.val,p.2.val) he _ _
      (by norm_num [meshPoint,macroCorner,cornerX,cornerY,strideX,strideY,Nat.mul_add])
      (by norm_num [macroCorner,cornerX,cornerY,strideX,strideY,Nat.mul_add])

private theorem cell_sides (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : Raster.Cell v.1) (c : Fin 4) (hc : c=1 ∨c=2) :
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f (meshPoint v.1 p))
      ((atlas v hP hT).profileAt f (macroCorner v.1 p c)) ∧
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f (macroCorner v.1 p c))
      ((atlas v hP hT).profileAt f (meshPoint v.1 p)) := by
  rcases cell_access v hP hT f p with he|⟨_,_,hr⟩
  · exact empty_sides v hP hT f p he c hc
  · exact ⟨(hr 0).2.trans (hr c).1,(hr c).2.trans (hr 0).1⟩

private theorem mesh_east (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : Raster.Cell v.1) (hx : p.1.val+1<Raster.width v.1) :
    let q : Raster.Cell v.1:=(⟨p.1.val+1,hx⟩,p.2)
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f (meshPoint v.1 p))
      ((atlas v hP hT).profileAt f (meshPoint v.1 q)) ∧
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f (meshPoint v.1 q))
      ((atlas v hP hT).profileAt f (meshPoint v.1 p)) := by
  dsimp only
  have hs:=cell_sides v hP hT f p 1 (Or.inl rfl)
  have hb:=east_bridge_walk v hP hT f (p.1.val,p.2.val) (macroCorner v.1 p 1)
    (meshPoint v.1 (⟨p.1.val+1,hx⟩,p.2))
    (by norm_num [macroCorner,cornerX,cornerY,strideX,strideY,Nat.mul_add])
    (by norm_num [meshPoint,macroCorner,cornerX,cornerY,strideX,strideY,Nat.mul_add])
  exact ⟨hs.1.trans hb.1,hb.2.trans hs.2⟩

private theorem mesh_south (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : Raster.Cell v.1) (hy : p.2.val+1<Raster.height v.1) :
    let q : Raster.Cell v.1:=(p.1,⟨p.2.val+1,hy⟩)
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f (meshPoint v.1 p))
      ((atlas v hP hT).profileAt f (meshPoint v.1 q)) ∧
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f (meshPoint v.1 q))
      ((atlas v hP hT).profileAt f (meshPoint v.1 p)) := by
  dsimp only
  have hs:=cell_sides v hP hT f p 2 (Or.inr rfl)
  have hb:=south_bridge_walk v hP hT f (p.1.val,p.2.val) (macroCorner v.1 p 2)
    (meshPoint v.1 (p.1,⟨p.2.val+1,hy⟩))
    (by norm_num [macroCorner,cornerX,cornerY,strideX,strideY,Nat.mul_add])
    (by norm_num [meshPoint,macroCorner,cornerX,cornerY,strideX,strideY,Nat.mul_add])
  exact ⟨hs.1.trans hb.1,hb.2.trans hs.2⟩

/-- Every actual source-grid corner is joined to the exterior player by literal whole-board walks. -/
private theorem profile_mesh (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped
    [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : Raster.Cell v.1) :
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f (atlas v hP hT).player)
      ((atlas v hP hT).profileAt f (meshPoint v.1 p)) ∧
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f (meshPoint v.1 p))
      ((atlas v hP hT).profileAt f (atlas v hP hT).player) := by
  let node (x : Fin (Raster.width v.1)) (y : Fin (Raster.height v.1)):=
    (atlas v hP hT).profileAt f (meshPoint v.1 (x,y))
  have hr:=MeshWalking.rectangle_positive (Raster.width_pos v.1) (Raster.height_pos v.1)
    (atlas v hP hT).board node (fun x hx y=>mesh_east v hP hT f (x,y) hx)
    (fun x y hy=>mesh_south v hP hT f (x,y) hy) p.1 p.2
  exact hr

/-- The exterior player reaches every actual complete tile hub and returns in every independently mixed profile. -/
theorem profile_hubs (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (i : Index v) :
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f (atlas v hP hT).player)
      ((atlas v hP hT).profileAt f ((embedding v i).cells (PhysicalTiles.piece (tile i)).initial.player)) ∧
    Reachable (atlas v hP hT).board (some 1)
      ((atlas v hP hT).profileAt f ((embedding v i).cells (PhysicalTiles.piece (tile i)).initial.player))
      ((atlas v hP hT).profileAt f (atlas v hP hT).player) := by
  rcases cell_access v hP hT f i.val.1 with he|⟨j,hj,hr⟩
  · exact (PhysicalTiles.key_nonempty (key_eq i) he).elim
  · have hji : j=i:=position_injective hj
    subst j
    have hm:=profile_mesh v hP hT f i.val.1
    exact ⟨hm.1.trans (hr 0).2,(hr 0).1.trans hm.2⟩

end PushPuzzle.PushFS.Reduction.PhysicalInventory
