/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceCoreGeometry
public import PushS.FiniteSourceChartLevels
public import PushS.FiniteSourceCertificate
public import PushS.FiniteGateRelay

/-! The actual compiled core supplies every static field of the successful-path gate reader. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory.CoreSite

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateMatching FiniteGateTracks
open FiniteGateStencils FiniteGateReadout FiniteCoreRails

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : CoreSite w hw v)

attribute [local irreducible] codes width height FiniteGeometry.side InventoryAssembly.board InventoryAssembly.walls

private theorem protection_rail : AndRail.main.cell w ⟨0,by simp [AndRail.count]⟩ = protectionCell w := by
  apply Prod.ext <;> apply Fin.ext <;> rfl

private theorem upper_rail : AndRail.input.cell w ⟨0,by simp [AndRail.count]⟩ = upperCornerCell w := by
  apply Prod.ext <;> apply Fin.ext <;> rfl

private theorem protection_center : (andProtectionCorner w).embedding.cells ((1,1) : Cell 3 3) = protectionCell w := by
  apply Prod.ext <;> apply Fin.ext
  · change origin w-6*w-10+1 = origin w-6*w-9
    unfold origin; omega
  · change origin w-1+1 = origin w
    unfold origin; omega

private theorem upper_center : (andUpperCorner w).embedding.cells ((1,1) : Cell 3 3) = upperCornerCell w := by
  apply Prod.ext <;> apply Fin.ext
  · change origin w-6*w-10+1 = origin w-6*w-9
    unfold origin; omega
  · change origin w-6*w-22+1 = origin w-6*w-21
    unfold origin; omega

theorem and_protection_name (hg : s.gate.core.isAND = true)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    (axisClassifier w hw v hP hT).name (s.embedding.cells (protectionCell w)) =
      .sink (s.embedding.cells (protectionCell w)).1.val (s.embedding.cells (protectionCell w)).2.val := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · cases hg
  · let s : CoreSite w hw v := ⟨index,⟨⟨true,initial,target⟩,incoming,pattern,rotation⟩,he⟩
    have hf := s.and_full_rail_floor rfl .main ⟨0,by simp [AndRail.count]⟩
    rw [protection_rail] at hf
    simp only [InventoryAssembly.board] at hf
    have hp : (primitiveEmbedding w hw v index (.core s.gate) he).cells
        (((PrimitiveCode.core s.gate).chart w hw .protectionCorner).embedding.cells ((1,1) : Cell 3 3)) ∉
        (inventory w hw v).walls := by
      change s.embedding.cells ((andProtectionCorner w).embedding.cells ((1,1) : Cell 3 3)) ∉ _
      rw [protection_center]
      exact hf
    have hn := primitive_chart_sink w hw v hP hT index (.core s.gate) he .protectionCorner
      ((1,1) : Cell 3 3) hp (by change (protectionClassifier.name ((1,1) : Cell 3 3)).level = 3; decide)
    change (axisClassifier w hw v hP hT).name
      (s.embedding.cells ((andProtectionCorner w).embedding.cells ((1,1) : Cell 3 3))) =
      .sink (s.embedding.cells ((andProtectionCorner w).embedding.cells ((1,1) : Cell 3 3))).1.val
        (s.embedding.cells ((andProtectionCorner w).embedding.cells ((1,1) : Cell 3 3))).2.val at hn
    simpa only [protection_center] using hn

theorem and_upper_name (hg : s.gate.core.isAND = true)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    (axisClassifier w hw v hP hT).name (s.embedding.cells (upperCornerCell w)) =
      .sink (s.embedding.cells (upperCornerCell w)).1.val (s.embedding.cells (upperCornerCell w)).2.val := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · cases hg
  · let s : CoreSite w hw v := ⟨index,⟨⟨true,initial,target⟩,incoming,pattern,rotation⟩,he⟩
    have hf := s.and_full_rail_floor rfl .input ⟨0,by simp [AndRail.count]⟩
    rw [upper_rail] at hf
    simp only [InventoryAssembly.board] at hf
    have hp : (primitiveEmbedding w hw v index (.core s.gate) he).cells
        (((PrimitiveCode.core s.gate).chart w hw .upperCorner).embedding.cells ((1,1) : Cell 3 3)) ∉
        (inventory w hw v).walls := by
      change s.embedding.cells ((andUpperCorner w).embedding.cells ((1,1) : Cell 3 3)) ∉ _
      rw [upper_center]
      exact hf
    have hn := primitive_chart_sink w hw v hP hT index (.core s.gate) he .upperCorner
      ((1,1) : Cell 3 3) hp (by change ((GuardStencils.cornerClassifier (1 : Fin 3) (1 : Fin 3)).name ((1,1) : Cell 3 3)).level = 3; decide)
    change (axisClassifier w hw v hP hT).name
      (s.embedding.cells ((andUpperCorner w).embedding.cells ((1,1) : Cell 3 3))) =
      .sink (s.embedding.cells ((andUpperCorner w).embedding.cells ((1,1) : Cell 3 3))).1.val
        (s.embedding.cells ((andUpperCorner w).embedding.cells ((1,1) : Cell 3 3))).2.val at hn
    simpa only [upper_center] using hn

theorem and_junction_name (hg : s.gate.core.isAND = true)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    (axisClassifier w hw v hP hT).name (s.embedding.cells (junctionCell w true)) = .horizontal (s.offsetY+origin w) := by
  have he : junctionCell w true = andCell w false false false .triggerA := rfl
  rw [he]
  exact s.and_axis_name hg hP hT false false false .triggerA

theorem or_junction_name (hg : s.gate.core.isAND = false)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    (axisClassifier w hw v hP hT).name (s.embedding.cells (junctionCell w false)) = .horizontal (s.offsetY+origin w) := by
  let i : Fin (OrRail.main.count w) := ⟨2*w+13,by simp [OrRail.count]; omega⟩
  let j : Fin (OrRail.main.count w) := ⟨2*w+12,by simp [OrRail.count]; omega⟩
  have hi : OrRail.main.cell w i = junctionCell w false := by
    apply Prod.ext
    · apply Fin.ext
      change origin w-2*w-9+(2*w+13) = origin w+4
      unfold origin; omega
    · rfl
  have hj : OrRail.main.cell w j = orCell w false false false .triggerA := by
    apply Prod.ext
    · apply Fin.ext
      change origin w-2*w-9+(2*w+12) = origin w+3
      unfold origin; omega
    · rfl
  have h := orRail_connected w .main s.embedding (inventory w hw v).board (s.or_full_rail_floor hg .main) i j
    (by dsimp [i,OrRail.count]; omega) (by dsimp [j,OrRail.count]; omega)
  rw [hi,hj] at h
  exact ((axisClassifier w hw v hP hT).name_eq_of_sameComponent h).trans
    (s.or_axis_name hg hP hT false false false .triggerA)

noncomputable def andBaseGlyph (hg : s.gate.core.isAND = true)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    ThickGateGlyph (slotMatching w hw v hP hT) (axisTracks w hw v hP hT) w true where
  dx := s.offsetX
  dy := s.offsetY
  fit_x := s.fits.1
  fit_y := s.fits.2
  initialSignals := s.gate.core.initial
  targetSignals := s.gate.core.target
  labels := ⟨s.andLabel hg,s.andLabel_injective hg⟩
  walls p hp := by
    change (GridEmbedding.translate s.offsetX s.offsetY s.fits.1 s.fits.2).cells p ∈ (inventory w hw v).board.walls
    rw [←s.embedding_translate]
    exact s.and_walls hg p hp
  sources l := by
    change (inventory w hw v).source (s.andLabel hg l) = (GridEmbedding.translate s.offsetX s.offsetY s.fits.1 s.fits.2).cells _
    rw [←s.embedding_translate]
    exact s.and_source_actual hg l
  targets l := by
    change (inventory w hw v).target (s.andLabel hg l) = (GridEmbedding.translate s.offsetX s.offsetY s.fits.1 s.fits.2).cells _
    rw [←s.embedding_translate]
    exact s.and_target_actual hg l
  tracks l := by
    change (axisClassifier w hw v hP hT).name ((inventory w hw v).source (s.andLabel hg l)) = _
    rw [s.and_source_actual]
    exact s.and_axis_name hg hP hT _ _ _ l
  junctionTag := by
    change (axisClassifier w hw v hP hT).name
      ((GridEmbedding.translate s.offsetX s.offsetY s.fits.1 s.fits.2).cells (junctionCell w true)) = _
    rw [←s.embedding_translate]
    exact s.and_junction_name hg hP hT

/-- Every field is derived from the actual table, full wall union and glued classifier. -/
noncomputable def andGlyph (hg : s.gate.core.isAND = true)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    AndGlyph (slotMatching w hw v hP hT) (axisTracks w hw v hP hT) w where
  toThickGateGlyph := s.andBaseGlyph hg hP hT
  protectedTag := by
    change (axisClassifier w hw v hP hT).name
      ((GridEmbedding.translate s.offsetX s.offsetY s.fits.1 s.fits.2).cells (protectionCell w)) =
      .sink (s.offsetX+origin w-6*w-9) (s.offsetY+origin w)
    rw [←s.embedding_translate,s.and_protection_name hg hP hT]
    apply congrArg₂ AxisTrack.sink
    · rw [s.embedding_x]
      change s.offsetX+(origin w-6*w-9) = s.offsetX+origin w-6*w-9
      unfold origin; omega
    · exact s.embedding_y _
  upperTag := by
    change (axisClassifier w hw v hP hT).name
      ((GridEmbedding.translate s.offsetX s.offsetY s.fits.1 s.fits.2).cells (upperCornerCell w)) =
      .sink (s.offsetX+origin w-6*w-9) (s.offsetY+origin w-6*w-21)
    rw [←s.embedding_translate,s.and_upper_name hg hP hT]
    apply congrArg₂ AxisTrack.sink
    · rw [s.embedding_x]
      change s.offsetX+(origin w-6*w-9) = s.offsetX+origin w-6*w-9
      unfold origin; omega
    · rw [s.embedding_y]
      change s.offsetY+(origin w-6*w-21) = s.offsetY+origin w-6*w-21
      unfold origin; omega
  railFloor r i := by
    change (GridEmbedding.translate s.offsetX s.offsetY s.fits.1 s.fits.2).cells (r.cell w i) ∉ (inventory w hw v).board.walls
    rw [←s.embedding_translate]
    exact s.and_full_rail_floor hg r i

noncomputable def orBaseGlyph (hg : s.gate.core.isAND = false)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    ThickGateGlyph (slotMatching w hw v hP hT) (axisTracks w hw v hP hT) w false where
  dx := s.offsetX
  dy := s.offsetY
  fit_x := s.fits.1
  fit_y := s.fits.2
  initialSignals := s.gate.core.initial
  targetSignals := s.gate.core.target
  labels := ⟨s.orLabel hg,s.orLabel_injective hg⟩
  walls p hp := by
    change (GridEmbedding.translate s.offsetX s.offsetY s.fits.1 s.fits.2).cells p ∈ (inventory w hw v).board.walls
    rw [←s.embedding_translate]
    exact s.or_walls hg p hp
  sources l := by
    change (inventory w hw v).source (s.orLabel hg l) = (GridEmbedding.translate s.offsetX s.offsetY s.fits.1 s.fits.2).cells _
    rw [←s.embedding_translate]
    exact s.or_source_actual hg l
  targets l := by
    change (inventory w hw v).target (s.orLabel hg l) = (GridEmbedding.translate s.offsetX s.offsetY s.fits.1 s.fits.2).cells _
    rw [←s.embedding_translate]
    exact s.or_target_actual hg l
  tracks l := by
    change (axisClassifier w hw v hP hT).name ((inventory w hw v).source (s.orLabel hg l)) = _
    rw [s.or_source_actual]
    exact s.or_axis_name hg hP hT _ _ _ l
  junctionTag := by
    change (axisClassifier w hw v hP hT).name
      ((GridEmbedding.translate s.offsetX s.offsetY s.fits.1 s.fits.2).cells (junctionCell w false)) = _
    rw [←s.embedding_translate]
    exact s.or_junction_name hg hP hT

noncomputable def orGlyph (hg : s.gate.core.isAND = false)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    OrGlyph (slotMatching w hw v hP hT) (axisTracks w hw v hP hT) w where
  toThickGateGlyph := s.orBaseGlyph hg hP hT
  railFloor r i := by
    change (GridEmbedding.translate s.offsetX s.offsetY s.fits.1 s.fits.2).cells (r.cell w i) ∉ (inventory w hw v).board.walls
    rw [←s.embedding_translate]
    exact s.or_full_rail_floor hg r i

end PushPuzzle.PushS.FiniteSourceInventory.CoreSite
