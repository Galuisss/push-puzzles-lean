/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceSafeCover

/-! The actual complete finite-force source wall union has its glued physical displacement classifier. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires GateTileRouting.FullGateStatics

attribute [local irreducible] codes width height InventoryAssembly.walls PrimitiveCode.instanceOf PrimitiveCode.chart

private theorem aligned_of_interior {w h W H : ℕ} (dx dy : ℕ) (p : Cell w h) (hp : Interior p) :
    Catalog.BoundaryAligned (W := W) (H := H) dx dy p := by
  dsimp only [Catalog.BoundaryAligned,Interior] at *
  omega

noncomputable def axisMosaic (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    Mosaic (inventory w hw v).board (Chart w v) :=
  Mosaic.of_floor_stencils (chart w hw v) (chart_walls w hw v) (by
    intro c p hp hf
    obtain ⟨d,q,hi,he,hl⟩ := chart_safe w hw v hP hT c p hp hf
    exact ⟨d,q,aligned_of_interior _ _ q hi,he,hl⟩)

/-- All C2 displacement classification data come from the literal emitted core, tool and rail walls. -/
noncomputable def axisClassifier (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) : AxisClassifier (inventory w hw v).board :=
  (axisMosaic w hw v hP hT).classifier

private theorem axis_chart_active (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (c : Chart w v)
    (p : Cell (chart w hw v c).width (chart w hw v c).height)
    (hp : (chart w hw v c).classifier.name p ≠ .outside)
    (hf : (chart w hw v c).embedding.cells p ∉ (inventory w hw v).walls) :
    (axisClassifier w hw v hP hT).name ((chart w hw v c).embedding.cells p) ≠ .outside := by
  have ha : ((axisMosaic w hw v hP hT).chart c).classifier.name p ≠ .outside := by
    simpa only [axisMosaic,Mosaic.of_floor_stencils,TranslatedAxisChart.restrictToFloor,
      TranslatedAxisChart.restrictTo,AxisClassifier.floorOnly,AxisClassifier.addWalls,GridEmbedding.pullback,
      InventoryAssembly.board,Finset.mem_filter,Finset.mem_univ,hf,and_false,ite_false] using hp
  exact (axisMosaic w hw v hP hT).source_active c p ha

theorem axis_actor_active (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (goal : Bool)
    (l : (inventory w hw v).PhysicalLabel) :
    (axisClassifier w hw v hP hT).name
      (if goal then (inventory w hw v).target l else (inventory w hw v).source l) ≠ .outside := by
  obtain ⟨c,p,he,hp⟩ := chart_actor w hw v goal l
  have hf : (chart w hw v c).embedding.cells p ∉ (inventory w hw v).walls := by
    rw [he]
    cases goal
    · exact source_floor w hw v l
    · exact target_floor w hw v l
  exact he ▸ axis_chart_active w hw v hP hT c p hp hf

theorem axis_initial_active (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p : Cell (width w v) (height w v)) (hp : p ∈ (inventory w hw v).initial.boxes) :
    (axisClassifier w hw v hP hT).name p ≠ .outside := by
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
  exact axis_actor_active w hw v hP hT false l

end PushPuzzle.PushS.FiniteSourceInventory
