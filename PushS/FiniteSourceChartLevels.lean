/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceAxisMosaic
public import PushS.FiniteSourceReadoutLabels

/-! Actual primitive stencils give their represented level in the complete source classifier. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting GateTileRouting.FullGateStatics

attribute [local irreducible] codes width height InventoryAssembly.walls InventoryAssembly.board

private theorem primitive_chart_level (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (i : Fin (codes w v).length) (c : PrimitiveCode) (hc : ((codes w v).get i).2 = c)
    (k : c.Charts) (p : Cell (c.chart w hw k).width (c.chart w hw k).height)
    (hf : (primitiveEmbedding w hw v i c hc).cells ((c.chart w hw k).embedding.cells p) ∉ (inventory w hw v).walls) :
    ((c.chart w hw k).classifier.name p).level ≤ ((axisClassifier w hw v hP hT).name
      ((primitiveEmbedding w hw v i c hc).cells ((c.chart w hw k).embedding.cells p))).level := by
  subst c
  let q := (primitiveEmbedding w hw v i ((codes w v).get i).2 rfl).cells
    ((((codes w v).get i).2.chart w hw k).embedding.cells p)
  have he : (chart w hw v ⟨i,k⟩).embedding.cells p = q :=
    (inventory w hw v).placedChart_cells i (((codes w v).get i).2.chart w hw k) p
  have hf' : (chart w hw v ⟨i,k⟩).embedding.cells p ∉ (inventory w hw v).walls := he ▸ hf
  have hn : ((axisMosaic w hw v hP hT).chart ⟨i,k⟩).classifier.name p =
      (((codes w v).get i).2.chart w hw k).classifier.name p := by
    simp only [axisMosaic,Mosaic.of_floor_stencils,TranslatedAxisChart.restrictToFloor,
      TranslatedAxisChart.restrictTo,AxisClassifier.floorOnly,AxisClassifier.addWalls,GridEmbedding.pullback,
      InventoryAssembly.board,Finset.mem_filter,Finset.mem_univ,hf',and_false,ite_false]
    rfl
  have hr : (axisMosaic w hw v hP hT).Represents q
      (AxisTrack.shift ((axisMosaic w hw v hP hT).chart ⟨i,k⟩).dx
        ((axisMosaic w hw v hP hT).chart ⟨i,k⟩).dy
        (((axisMosaic w hw v hP hT).chart ⟨i,k⟩).classifier.name p)) := ⟨⟨i,k⟩,p,he,rfl⟩
  have hl := (axisMosaic w hw v hP hT).represented_le hr
  change _ ≤ ((axisMosaic w hw v hP hT).name q).level
  simpa only [AxisTrack.level_shift,hn] using hl

theorem primitive_chart_sink (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (i : Fin (codes w v).length) (c : PrimitiveCode) (hc : ((codes w v).get i).2 = c)
    (k : c.Charts) (p : Cell (c.chart w hw k).width (c.chart w hw k).height)
    (hf : (primitiveEmbedding w hw v i c hc).cells ((c.chart w hw k).embedding.cells p) ∉ (inventory w hw v).walls)
    (ht : ((c.chart w hw k).classifier.name p).level = 3) :
    let q := (primitiveEmbedding w hw v i c hc).cells ((c.chart w hw k).embedding.cells p)
    (axisClassifier w hw v hP hT).name q = .sink q.1.val q.2.val := by
  dsimp only
  have hl := primitive_chart_level w hw v hP hT i c hc k p hf
  rw [ht] at hl
  have hs := (axisClassifier w hw v hP hT).supported
    ((primitiveEmbedding w hw v i c hc).cells ((c.chart w hw k).embedding.cells p))
  cases hn : (axisClassifier w hw v hP hT).name
      ((primitiveEmbedding w hw v i c hc).cells ((c.chart w hw k).embedding.cells p)) <;>
    simp only [hn,AxisTrack.level] at hl
  all_goals first
    | omega
    | simp only [hn,AxisTrack.Supports] at hs
      exact congrArg₂ AxisTrack.sink hs.1.symm hs.2.symm

end PushPuzzle.PushS.FiniteSourceInventory
