/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalMesh
public import PushFS.Gadgets.Wires.Catalog.ExteriorWalking
public import PushFS.Reduction.PhysicalProfilePlacements
public import PushFS.Reduction.PhysicalWireSignals
public import PushFS.Reduction.PhysicalWireForeign

/-! Complete ordinary-tile corner walks transported to the actual whole-board mixed inventory. -/
@[expose] public section
namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open PhysicalBitmap Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board
  StorageAtlas.profileOutside StorageAtlas.profileBoxes PhysicalTiles.marks Polyline.Frame.fixed

/-- Every local walk with its exact actual foreign preimage is a walk of the complete atlas. -/
private theorem wire_profile_walk (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : Raster.Cell v.1) (a : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a)) (s t : Catalog.Cell)
    (hr :
      let i:=wireIndex v p a ha
      let fixed:=Polyline.Frame.fixed (embedding v i) ((atlas v hP hT).profileOutside f (numbering v i))
      Reachable (Catalog.puzzle a.1 a.2.1 a.2.2).board (some 1)
        ⟨s,PhysicalTiles.marks (f (numbering v i)) (.inr a)∪fixed⟩
        ⟨t,PhysicalTiles.marks (f (numbering v i)) (.inr a)∪fixed⟩) :
    Reachable (atlas v hP hT).board (some 1)
      ((atlas v hP hT).profileAt f ((embedding v (wireIndex v p a ha)).cells s))
      ((atlas v hP hT).profileAt f ((embedding v (wireIndex v p a ha)).cells t)) := by
  let i:=wireIndex v p a ha
  let e:=embedding v i
  let outside:=(atlas v hP hT).profileOutside f (numbering v i)
  have hw : e.WallsAgree (Catalog.puzzle a.1 a.2.1 a.2.2).board (atlas v hP hT).board := by
    intro q
    exact walls_agree v hP hT i q
  have hh:=e.reachable_withFixed (s:=⟨s,PhysicalTiles.marks (f (numbering v i)) (.inr a)⟩)
    (t:=⟨t,PhysicalTiles.marks (f (numbering v i)) (.inr a)⟩) hw
    (fun q hq=>(@Polyline.Frame.mem_fixed Catalog.width Catalog.height
      (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7) e outside q).mpr hq)
    (fun q hq=>(@Polyline.Frame.mem_fixed Catalog.width Catalog.height
      (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7) e outside q).mp hq)
    ((atlas v hP hT).profileOutside_floor f (numbering v i)) hr
  have hs:=profile_place_index v hP hT f i s
  have ht:=profile_place_index v hP hT f i t
  exact Eq.mp (congrArg₂ (Reachable (atlas v hP hT).board (some 1)) hs ht) hh

/-- The complete selected ordinary inventory reaches every literal macrocell corner. -/
private theorem wire_profile_corners_of_mask (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : Raster.Cell v.1) (a : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a))
    (hm : ∀q : Catalog.Cell,(embedding v (wireIndex v p a ha)).cells q∈
      (atlas v hP hT).profileOutside f (numbering v (wireIndex v p a ha))→Catalog.WalkingMask a.1 q)
    (c : Fin 4) :
    Reachable (atlas v hP hT).board (some 1)
      ((atlas v hP hT).profileAt f ((embedding v (wireIndex v p a ha)).cells (Catalog.puzzle a.1 a.2.1 a.2.2).initial.player))
      ((atlas v hP hT).profileAt f (macroCorner v.1 p c)) ∧
    Reachable (atlas v hP hT).board (some 1)
      ((atlas v hP hT).profileAt f (macroCorner v.1 p c))
      ((atlas v hP hT).profileAt f ((embedding v (wireIndex v p a ha)).cells (Catalog.puzzle a.1 a.2.1 a.2.2).initial.player)) := by
  let i:=wireIndex v p a ha
  let e:=embedding v i
  let outside:=(atlas v hP hT).profileOutside f (numbering v i)
  let fixed:=Polyline.Frame.fixed e outside
  have hm' : ∀q∈fixed,Catalog.WalkingMask a.1 q:=by
    intro q hq
    exact hm q ((@Polyline.Frame.mem_fixed Catalog.width Catalog.height
      (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7) e outside q).mp hq)
  have hh:=Catalog.selected_corners a.1 a.2.1 a.2.2 (f (numbering v i)) fixed hm' c
  have hmarks : @Eq (Finset Catalog.Cell) (PhysicalTiles.marks (f (numbering v i)) (.inr a))
      (if f (numbering v i) then (Catalog.puzzle a.1 a.2.1 a.2.2).board.goals else (Catalog.puzzle a.1 a.2.1 a.2.2).initial.boxes) := by
    unfold PhysicalTiles.marks
    rfl
  have hs (q : Catalog.Cell) : (⟨q,(if f (numbering v i) then (Catalog.puzzle a.1 a.2.1 a.2.2).board.goals else
      (Catalog.puzzle a.1 a.2.1 a.2.2).initial.boxes)∪fixed⟩ : State Catalog.width Catalog.height)=
        ⟨q,PhysicalTiles.marks (f (numbering v i)) (.inr a)∪fixed⟩ :=
    State.ext rfl (congrArg (fun xs : Finset Catalog.Cell=>xs∪fixed) hmarks.symm)
  have hlocal₁:=Eq.mp (congrArg₂ (@Reachable Catalog.width Catalog.height (Catalog.puzzle a.1 a.2.1 a.2.2).board (some 1)) (hs _) (hs _)) hh.1
  have hlocal₂:=Eq.mp (congrArg₂ (@Reachable Catalog.width Catalog.height (Catalog.puzzle a.1 a.2.1 a.2.2).board (some 1)) (hs _) (hs _)) hh.2
  have h₁:=wire_profile_walk v hP hT f p a ha _ _ hlocal₁
  have h₂:=wire_profile_walk v hP hT f p a ha _ _ hlocal₂
  have he : e.cells (Catalog.outerCorner c)=macroCorner v.1 p c:=embedding_corner v i c
  rw [he] at h₁ h₂
  exact ⟨h₁,h₂⟩

/-- Every ordinary macrocell has actual four-corner access in every whole-board mixed profile. -/
theorem wire_profile_corners (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : Raster.Cell v.1) (a : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a)) (c : Fin 4) :
    Reachable (atlas v hP hT).board (some 1)
      ((atlas v hP hT).profileAt f ((embedding v (wireIndex v p a ha)).cells (Catalog.puzzle a.1 a.2.1 a.2.2).initial.player))
      ((atlas v hP hT).profileAt f (macroCorner v.1 p c)) ∧
    Reachable (atlas v hP hT).board (some 1)
      ((atlas v hP hT).profileAt f (macroCorner v.1 p c))
      ((atlas v hP hT).profileAt f ((embedding v (wireIndex v p a ha)).cells (Catalog.puzzle a.1 a.2.1 a.2.2).initial.player)) :=
  wire_profile_corners_of_mask v hP hT f p a ha (wire_foreign_walkingMask v hP hT f p a ha) c

end PushPuzzle.PushFS.Reduction.PhysicalInventory
