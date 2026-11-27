/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalAxisContacts
public import PushFS.Reduction.PhysicalRawLabels

/-! Supported wall-only displacement classification of the complete physical source board. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL PhysicalBitmap Gadgets.Wires GateTileRouting.FullGateStatics
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

private theorem aligned_of_interior {w h W H : ℕ} (dx dy : ℕ) (p : Cell w h) (hp : Interior p) :
    Catalog.BoundaryAligned (W:=W) (H:=H) dx dy p := by
  dsimp only [Catalog.BoundaryAligned,Interior] at *
  omega

noncomputable def axisMosaic (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) :
    Mosaic (W:=strideX*Raster.width v.1+7) (H:=strideY*Raster.height v.1+7) (puzzle v hP hT).board (Index v) where
  chart:=axisChart v
  walls:=axisChart_walls v hP hT
  safe i p ha:=by
    by_cases hi : Interior p
    · exact ⟨i,p,aligned_of_interior _ _ p hi,rfl,le_refl _⟩
    · obtain ⟨bp⟩:=PhysicalTiles.boundary_port (tile i) p ha hi
      obtain ⟨j,hn,hu⟩:=used_neighbor v hP hT i bp.direction bp.used
      have hr : (PhysicalTiles.portName (tile i) bp.direction).Supports p :=
        bp.name ▸(PhysicalTiles.classifier (tile i)).supported p
      obtain ⟨contact⟩:=PhysicalTiles.port_contact (position i) (position j) (tile i) (tile j)
        bp.direction hn p bp.side hr
      refine ⟨j,contact.cell,aligned_of_interior _ _ _ contact.interior,?_,?_⟩
      · apply Prod.ext <;> apply Fin.ext
        · exact congrArg Prod.fst contact.coordinates
        · exact congrArg Prod.snd contact.coordinates
      · change ((PhysicalTiles.classifier (tile i)).name p).level≤
          ((PhysicalTiles.classifier (tile j)).name contact.cell).level
        rw [bp.name]
        have he : (PhysicalTiles.portName (tile i) bp.direction).level=
            (PhysicalTiles.portName (tile j) bp.direction.opposite).level := by
          cases bp.direction <;> rfl
        rw [he]
        exact PhysicalTiles.port_level (tile j) bp.direction.opposite contact.cell hu contact.collar contact.rail

noncomputable def axisClassifier (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) :
    AxisClassifier (puzzle v hP hT).board := (axisMosaic v hP hT).classifier

theorem axis_initial_active (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (p : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hp : p∈(puzzle v hP hT).initial.boxes) : (axisClassifier v hP hT).name p≠.outside := by
  rw [←(rawSlotMatching v hP hT).source_image] at hp
  obtain ⟨⟨i,l⟩,_,rfl⟩:=Finset.mem_map.mp hp
  have hl : (PhysicalTiles.matching (tile i)).source l∈(PhysicalTiles.piece (tile i)).initial.boxes := by
    rw [←(PhysicalTiles.matching (tile i)).source_image]
    exact Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩
  have ht:=(axisMosaic v hP hT).source_active i _ (PhysicalTiles.initial_active (tile i) _ hl)
  have he:=congrArg (axisClassifier v hP hT).name (raw_source v hP hT i l)
  exact he.symm ▸ht

/-- C2 holds for every actual initial box in the complete source-to-physical compiler. -/
theorem componentLinear (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (p : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hp : p∈(puzzle v hP hT).initial.boxes) : ComponentLinear (component (puzzle v hP hT).board p) :=
  active_linear (axisClassifier v hP hT) p (axis_initial_active v hP hT p hp)

end PushPuzzle.PushFS.Reduction.PhysicalInventory
