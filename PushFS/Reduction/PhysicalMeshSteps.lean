/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalMeshFloor
public import PushFS.Reduction.PhysicalMesh

/-! Actual fixed-box paths along empty macrocell sides and short corner bridges. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL PhysicalBitmap Gadgets.Wires
set_option maxRecDepth 65536
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board StorageAtlas.profileBoxes

private theorem row_both {W H : ℕ} (B : Board W H) (xs : Finset (Cell W H)) (hf : Disjoint xs B.walls)
    (p q : Cell W H) (hy : p.2=q.2)
    (hfree : ∀x : Fin W,min p.1.val q.1.val≤x.val→x.val≤max p.1.val q.1.val→Free B xs (x,p.2)) :
    Reachable B (some 1) ⟨p,xs⟩ ⟨q,xs⟩ ∧Reachable B (some 1) ⟨q,xs⟩ ⟨p,xs⟩ := by
  have he : q=(q.1,p.2):=Prod.ext rfl hy.symm
  rw [he]
  exact ⟨walk_horizontal hf p.1 q.1 p.2 hfree,
    walk_horizontal hf q.1 p.1 p.2 (fun x hlo hhi=>hfree x (by omega) (by omega))⟩

private theorem col_both {W H : ℕ} (B : Board W H) (xs : Finset (Cell W H)) (hf : Disjoint xs B.walls)
    (p q : Cell W H) (hx : p.1=q.1)
    (hfree : ∀y : Fin H,min p.2.val q.2.val≤y.val→y.val≤max p.2.val q.2.val→Free B xs (p.1,y)) :
    Reachable B (some 1) ⟨p,xs⟩ ⟨q,xs⟩ ∧Reachable B (some 1) ⟨q,xs⟩ ⟨p,xs⟩ := by
  have he : q=(p.1,q.2):=Prod.ext hx.symm rfl
  rw [he]
  exact ⟨walk_vertical hf p.1 p.2 q.2 hfree,
    walk_vertical hf p.1 q.2 p.2 (fun y hlo hhi=>hfree y (by omega) (by omega))⟩

/-- Both directions of the literal empty top walk keep every physical box fixed. -/
theorem empty_top_walk (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (origin : GridRouting.Point)
    (hempty : CellPlan.cell (v,origin)=none)
    (p q : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hp : strideX*origin.1+1≤p.1.val ∧p.1.val≤strideX*origin.1+200005 ∧p.2.val=strideY*origin.2+1)
    (hq : strideX*origin.1+1≤q.1.val ∧q.1.val≤strideX*origin.1+200005 ∧q.2.val=strideY*origin.2+1) :
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f p) ((atlas v hP hT).profileAt f q) ∧
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f q) ((atlas v hP hT).profileAt f p) := by
  apply row_both (atlas v hP hT).board ((atlas v hP hT).profileBoxes f) ((atlas v hP hT).profile_floor f) p q
  · exact Fin.ext (hp.2.2.trans hq.2.2.symm)
  · intro t hlo hhi
    apply empty_top_free v hP hT f origin hempty (t,p.2)
    · dsimp only
      omega
    · dsimp only
      omega
    · exact hp.2.2

/-- Both directions of the literal empty left walk keep every physical box fixed. -/
theorem empty_left_walk (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (origin : GridRouting.Point)
    (hempty : CellPlan.cell (v,origin)=none)
    (p q : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hp : strideY*origin.2+1≤p.2.val ∧p.2.val≤strideY*origin.2+198066 ∧p.1.val=strideX*origin.1+1)
    (hq : strideY*origin.2+1≤q.2.val ∧q.2.val≤strideY*origin.2+198066 ∧q.1.val=strideX*origin.1+1) :
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f p) ((atlas v hP hT).profileAt f q) ∧
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f q) ((atlas v hP hT).profileAt f p) := by
  apply col_both (atlas v hP hT).board ((atlas v hP hT).profileBoxes f) ((atlas v hP hT).profile_floor f) p q
  · exact Fin.ext (hp.2.2.trans hq.2.2.symm)
  · intro t hlo hhi
    apply empty_left_free v hP hT f origin hempty (p.1,t)
    · dsimp only
      omega
    · dsimp only
      omega
    · exact hp.2.2

/-- Both directions of the literal east bridge walk keep every physical box fixed. -/
theorem east_bridge_walk (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (origin : GridRouting.Point)
    (p q : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hp : strideX*origin.1+200001≤p.1.val ∧p.1.val≤strideX*origin.1+200005 ∧p.2.val=strideY*origin.2+1)
    (hq : strideX*origin.1+200001≤q.1.val ∧q.1.val≤strideX*origin.1+200005 ∧q.2.val=strideY*origin.2+1) :
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f p) ((atlas v hP hT).profileAt f q) ∧
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f q) ((atlas v hP hT).profileAt f p) := by
  apply row_both (atlas v hP hT).board ((atlas v hP hT).profileBoxes f) ((atlas v hP hT).profile_floor f) p q
  · exact Fin.ext (hp.2.2.trans hq.2.2.symm)
  · intro t hlo hhi
    apply east_bridge_free v hP hT f origin (t,p.2)
    · dsimp only
      omega
    · dsimp only
      omega
    · exact hp.2.2

/-- Both directions of the literal south bridge walk keep every physical box fixed. -/
theorem south_bridge_walk (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (origin : GridRouting.Point)
    (p q : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hp : strideY*origin.2+198062≤p.2.val ∧p.2.val≤strideY*origin.2+198066 ∧p.1.val=strideX*origin.1+1)
    (hq : strideY*origin.2+198062≤q.2.val ∧q.2.val≤strideY*origin.2+198066 ∧q.1.val=strideX*origin.1+1) :
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f p) ((atlas v hP hT).profileAt f q) ∧
    Reachable (atlas v hP hT).board (some 1) ((atlas v hP hT).profileAt f q) ((atlas v hP hT).profileAt f p) := by
  apply col_both (atlas v hP hT).board ((atlas v hP hT).profileBoxes f) ((atlas v hP hT).profile_floor f) p q
  · exact Fin.ext (hp.2.2.trans hq.2.2.symm)
  · intro t hlo hhi
    apply south_bridge_free v hP hT f origin (p.1,t)
    · dsimp only
      omega
    · dsimp only
      omega
    · exact hp.2.2

end PushPuzzle.PushFS.Reduction.PhysicalInventory
