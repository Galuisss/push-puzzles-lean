/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateRelay

/-! Both actual thick AND corners transmit their successful-path thresholds. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateReadout.AndGlyph

open PushFS PushFS.Gadgets FiniteGeometry FiniteGateCore FiniteGateTracks
open PushFS.Gadgets.Wires.Soundness PushFS.Gadgets.Wires.Polyline
open PushFS.Gadgets.Gates.Soundness.Relay

variable {I : PushFS.Instance} {Label : Type} [Fintype Label]
    {M : SlotMatching I Label} {A : AxisTracks I} {w : ℕ}
    (g : AndGlyph M A w) {S final : LabelledState Label I.width I.height}

attribute [local irreducible] side

theorem input_track (l : AndLabel w) (hl : FiniteCoreRails.andRail l = .input) :
    A.name (M.source (g.labels l)) = .vertical g.mainX := by
  rw [g.tracks]
  cases l <;> simp [FiniteCoreRails.andRail] at hl <;> rfl

private theorem mainY_bound : g.mainY+1 < I.height := by
  have hf := g.fit_y
  unfold mainY
  unfold origin side at *
  omega

private theorem lower_vertical_above (h : Successful M S final) :
    (S.position (g.labels (.lower ⟨w+4, by omega⟩))).2.val < g.mainY := by
  have ht := g.input_track (.lower ⟨w+4, by omega⟩) rfl
  have hn : A.name (g.toThickGateGlyph.embedding.cells (protectionCell w)) ≠
      A.name (M.source (g.labels (.lower ⟨w+4, by omega⟩))) := by
    unfold ThickGateGlyph.embedding
    rw [g.protectedTag, ht]
    exact AxisTrack.noConfusion
  have hb : coord false (M.source (g.labels (.lower ⟨w+4, by omega⟩))) <
      coord false (g.toThickGateGlyph.embedding.cells (protectionCell w)) := by
    rw [g.sources]
    have ha := Bool.toNat_le g.initialSignals.left
    dsimp [coord, ThickGateGlyph.embedding, GridEmbedding.translate, protectionCell,
      gateCell, andCell, andPoint, origin]
    omega
  exact h.below_barrier A false g.mainX _ ht
    (g.toThickGateGlyph.embedding.cells (protectionCell w)) rfl hn hb

private theorem protection_corner_walls (hw : 2 ≤ w) :
    Corner.Walls ((GridIsometry.reflectY I.width I.height).board I.board)
      g.mainX (I.height-(g.mainY+1)) := by
  have hY := g.mainY_bound
  constructor
  · intro p hx hy
    obtain ⟨q, rfl⟩ := (GridIsometry.reflectY I.width I.height).cells.surjective p
    apply (GridIsometry.mem_walls _ _ _).mpr
    change q.1.val = g.mainX at hx
    change I.height-(q.2.val+1)+1 = I.height-(g.mainY+1) at hy
    have hqY := q.2.isLt
    apply g.wall_rectangle 0 q
    all_goals simp [andRectangle, mainX, mainY, origin] at *; omega
  · intro p hx hy
    obtain ⟨q, rfl⟩ := (GridIsometry.reflectY I.width I.height).cells.surjective p
    apply (GridIsometry.mem_walls _ _ _).mpr
    change q.1.val+1 = g.mainX at hx
    change I.height-(q.2.val+1) = I.height-(g.mainY+1) at hy
    have hqY := q.2.isLt
    apply g.wall_rectangle 1 q
    all_goals simp [andRectangle, mainX, mainY, origin] at *; omega

/-- The protected lower corner cannot seal between its real horizontal and vertical labels. -/
theorem protection_corner_good (h : Successful M S final) (cert : Certificate I)
    (ho : M.Ordered) (hw : 2 ≤ w) :
    g.mainX+2 ≤ (S.position (g.guard 0)).1.val ∨
      (S.position (g.labels (.lower ⟨w+4, by omega⟩))).2.val+2 ≤ g.mainY := by
  let e := GridIsometry.reflectY I.width I.height
  let F := g.guard 0
  let G := g.labels (.lower ⟨w+4, by omega⟩)
  let y := I.height-(g.mainY+1)
  have hY := g.mainY_bound
  have htF := g.track_guard 0
  have htG := g.input_track (.lower ⟨w+4, by omega⟩) rfl
  have shape U (hu : Successful M U final) :
      Corner.Shape g.mainX y (pair (I := e.reorientInstance I) (orientLabels e U) F G) := by
    have hrow := hu.line A true g.mainY F htF
    have hcol := hu.line A false g.mainX G htG
    have hF := g.first_guard_lower hu
    have hG := g.lower_vertical_above hu
    refine ⟨(orientLabels e U).position_mem F, (orientLabels e U).position_mem G, ?_, ?_, ?_, ?_⟩
    · change I.height-((U.position F).2.val+1) = y
      change (U.position F).2.val = g.mainY at hrow
      rw [hrow]
    · change g.mainX < (U.position F).1.val
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hF
    · exact hcol
    · change y < I.height-((U.position G).2.val+1)
      have hy := (U.position G).2.isLt
      dsimp [y, G] at *
      omega
  have normal (bits : Gates.Signals) :
      g.mainX+1 < (e.cells (g.toThickGateGlyph.embedding.cells
        (andCell w bits.left bits.upper bits.right (.guard 0)))).1.val ∨
      y+1 < (e.cells (g.toThickGateGlyph.embedding.cells
        (andCell w bits.left bits.upper bits.right (.lower ⟨w+4, by omega⟩)))).2.val := by
    change g.mainX+1 < g.dx+(andCell w bits.left bits.upper bits.right (.guard 0)).1.val ∨
      y+1 < I.height-(g.dy+(andCell w bits.left bits.upper bits.right (.lower ⟨w+4, by omega⟩)).2.val+1)
    cases bits.left <;> simp [andCell, andPoint] <;>
      dsimp [mainX, mainY, y] at * <;> unfold origin at * <;> omega
  have hstart : g.mainX+1 < (e.cells (M.source F)).1.val ∨ y+1 < (e.cells (M.source G)).2.val := by
    change _ < (e.cells (M.source (g.labels (.guard 0)))).1.val ∨
      _ < (e.cells (M.source (g.labels (.lower ⟨w+4, by omega⟩)))).2.val
    rw [g.sources, g.sources]
    exact normal g.initialSignals
  have hfinish : g.mainX+1 < (e.cells (M.target F)).1.val ∨ y+1 < (e.cells (M.target G)).2.val := by
    change _ < (e.cells (M.target (g.labels (.guard 0)))).1.val ∨
      _ < (e.cells (M.target (g.labels (.lower ⟨w+4, by omega⟩)))).2.val
    rw [g.targets, g.targets]
    exact normal g.targetSignals
  have hg := oriented_corner_good h cert ho e g.mainX y F G
    (g.protection_corner_walls hw) shape hstart hfinish
  change g.mainX+1 < (S.position F).1.val ∨ y+1 < I.height-((S.position G).2.val+1) at hg
  have hy := (S.position G).2.isLt
  dsimp [y] at hg
  change g.mainX+2 ≤ (S.position F).1.val ∨ (S.position G).2.val+2 ≤ g.mainY
  omega

private theorem west_track (i : Fin (w+4)) :
    A.name (M.source (g.labels (.west i))) = .horizontal g.upperY := by
  rw [g.tracks]
  rfl

private theorem mainX_bound : g.mainX+1 < I.width := by
  have hf := g.fit_x
  unfold mainX
  unfold origin side at *
  omega

private theorem upper_corner_bounds (h : Successful M S final) :
    (S.position (g.labels (.west 0))).1.val < g.mainX ∧
      g.upperY < (S.position (g.labels (.upper 0))).2.val := by
  have htF := g.west_track 0
  have htG := g.input_track (.upper 0) rfl
  have hnF : A.name (g.toThickGateGlyph.embedding.cells (upperCornerCell w)) ≠
      A.name (M.source (g.labels (.west 0))) := by
    unfold ThickGateGlyph.embedding
    rw [g.upperTag, htF]
    exact AxisTrack.noConfusion
  have hnG : A.name (g.toThickGateGlyph.embedding.cells (upperCornerCell w)) ≠
      A.name (M.source (g.labels (.upper 0))) := by
    unfold ThickGateGlyph.embedding
    rw [g.upperTag, htG]
    exact AxisTrack.noConfusion
  have hsF : coord true (M.source (g.labels (.west 0))) <
      coord true (g.toThickGateGlyph.embedding.cells (upperCornerCell w)) := by
    rw [g.sources]
    have ha := Bool.toNat_le g.initialSignals.left
    dsimp [coord, ThickGateGlyph.embedding, GridEmbedding.translate, upperCornerCell,
      gateCell, andCell, andPoint, origin]
    omega
  have hsG : coord false (g.toThickGateGlyph.embedding.cells (upperCornerCell w)) <
      coord false (M.source (g.labels (.upper 0))) := by
    rw [g.sources]
    have ha := Bool.toNat_le g.initialSignals.left
    dsimp [coord, ThickGateGlyph.embedding, GridEmbedding.translate, upperCornerCell,
      gateCell, andCell, andPoint, origin]
    omega
  exact ⟨h.below_barrier A true g.upperY _ htF
    (g.toThickGateGlyph.embedding.cells (upperCornerCell w)) rfl hnF hsF,
    h.above_barrier A false g.mainX _ htG
      (g.toThickGateGlyph.embedding.cells (upperCornerCell w)) rfl hnG hsG⟩

private theorem upper_corner_walls (hw : 2 ≤ w) :
    Corner.Walls ((GridIsometry.reflectX I.width I.height).board I.board)
      (I.width-(g.mainX+1)) g.upperY := by
  have hX := g.mainX_bound
  constructor
  · intro p hx hy
    obtain ⟨q, rfl⟩ := (GridIsometry.reflectX I.width I.height).cells.surjective p
    apply (GridIsometry.mem_walls _ _ _).mpr
    change I.width-(q.1.val+1) = I.width-(g.mainX+1) at hx
    change q.2.val+1 = g.upperY at hy
    have hqX := q.1.isLt
    apply g.wall_rectangle 5 q
    all_goals simp [andRectangle, mainX, upperY, origin] at *; omega
  · intro p hx hy
    obtain ⟨q, rfl⟩ := (GridIsometry.reflectX I.width I.height).cells.surjective p
    apply (GridIsometry.mem_walls _ _ _).mpr
    change I.width-(q.1.val+1)+1 = I.width-(g.mainX+1) at hx
    change q.2.val = g.upperY at hy
    have hqX := q.1.isLt
    apply g.wall_rectangle 4 q
    all_goals simp [andRectangle, mainX, upperY, origin] at *; omega

/-- The upper turn's successful-path obstruction transmits the vertical threshold to the west rail. -/
theorem upper_corner_good (h : Successful M S final) (cert : Certificate I)
    (ho : M.Ordered) (hw : 2 ≤ w) :
    (S.position (g.labels (.west 0))).1.val+2 ≤ g.mainX ∨
      g.upperY+2 ≤ (S.position (g.labels (.upper 0))).2.val := by
  let e := GridIsometry.reflectX I.width I.height
  let F := g.labels (.west 0)
  let G := g.labels (.upper 0)
  let j := I.width-(g.mainX+1)
  have hX := g.mainX_bound
  have htF := g.west_track 0
  have htG := g.input_track (.upper 0) rfl
  have shape U (hu : Successful M U final) :
      Corner.Shape j g.upperY (pair (I := e.reorientInstance I) (orientLabels e U) F G) := by
    have hrow := hu.line A true g.upperY F htF
    have hcol := hu.line A false g.mainX G htG
    have hFG := g.upper_corner_bounds hu
    refine ⟨(orientLabels e U).position_mem F, (orientLabels e U).position_mem G, hrow, ?_, ?_, hFG.2⟩
    · change j < I.width-((U.position F).1.val+1)
      have hx := (U.position F).1.isLt
      have hF := hFG.1
      change (U.position F).1.val < g.mainX at hF
      dsimp [j]
      omega
    · change I.width-((U.position G).1.val+1) = j
      change (U.position G).1.val = g.mainX at hcol
      rw [hcol]
  have normal (bits : Gates.Signals) :
      j+1 < (e.cells (g.toThickGateGlyph.embedding.cells
        (andCell w bits.left bits.upper bits.right (.west 0)))).1.val ∨
      g.upperY+1 < (e.cells (g.toThickGateGlyph.embedding.cells
        (andCell w bits.left bits.upper bits.right (.upper 0)))).2.val := by
    change j+1 < I.width-(g.dx+(andCell w bits.left bits.upper bits.right (.west 0)).1.val+1) ∨
      g.upperY+1 < g.dy+(andCell w bits.left bits.upper bits.right (.upper 0)).2.val
    cases bits.left <;> simp [andCell, andPoint] <;>
      dsimp [mainX, upperY, j] at * <;> unfold origin at * <;> omega
  have hstart : j+1 < (e.cells (M.source F)).1.val ∨ g.upperY+1 < (e.cells (M.source G)).2.val := by
    change _ < (e.cells (M.source (g.labels (.west 0)))).1.val ∨
      _ < (e.cells (M.source (g.labels (.upper 0)))).2.val
    rw [g.sources, g.sources]
    exact normal g.initialSignals
  have hfinish : j+1 < (e.cells (M.target F)).1.val ∨ g.upperY+1 < (e.cells (M.target G)).2.val := by
    change _ < (e.cells (M.target (g.labels (.west 0)))).1.val ∨
      _ < (e.cells (M.target (g.labels (.upper 0)))).2.val
    rw [g.targets, g.targets]
    exact normal g.targetSignals
  have hg := oriented_corner_good h cert ho e j g.upperY F G
    (g.upper_corner_walls hw) shape hstart hfinish
  change j+1 < I.width-((S.position F).1.val+1) ∨ g.upperY+1 < (S.position G).2.val at hg
  have hx := (S.position F).1.isLt
  dsimp [j] at hg
  change (S.position F).1.val+2 ≤ g.mainX ∨ g.upperY+2 ≤ (S.position G).2.val
  omega

end PushPuzzle.PushS.FiniteGateReadout.AndGlyph
