/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateCorners

/-! The two real thick islands transmit the AND input signal through arbitrary middle-box offsets. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateReadout.AndGlyph

open PushFS PushFS.Gadgets FiniteGeometry FiniteGateCore
open PushFS.Gadgets.Wires.Soundness PushFS.Gadgets.Gates.Soundness.Relay

variable {I : PushFS.Instance} {Label : Type} [Fintype Label]
    {M : SlotMatching I Label} {A : AxisTracks I} {w : ℕ}
    (g : AndGlyph M A w) {S final : LabelledState Label I.width I.height}

attribute [local irreducible] side

private theorem lower_flip_strip (hw : 2 ≤ w) :
    StripWalls ((GridIsometry.transpose I.width I.height).board I.board)
      g.flipY (g.flipY+w-2) g.mainX := by
  constructor
  · intro p hx hy hy'
    obtain ⟨q, rfl⟩ := (GridIsometry.transpose I.width I.height).cells.surjective p
    apply (GridIsometry.mem_walls _ _ _).mpr
    change q.1.val = g.mainX+1 at hx
    change g.flipY ≤ q.2.val at hy
    change q.2.val ≤ g.flipY+w-2 at hy'
    apply g.wall_rectangle 3 q
    all_goals simp [andRectangle, mainX, flipY, origin] at *; omega
  · intro p hx hy hy'
    obtain ⟨q, rfl⟩ := (GridIsometry.transpose I.width I.height).cells.surjective p
    apply (GridIsometry.mem_walls _ _ _).mpr
    change q.1.val+1 = g.mainX at hx
    change g.flipY ≤ q.2.val at hy
    change q.2.val ≤ g.flipY+w-2 at hy'
    apply g.wall_rectangle 1 q
    all_goals simp [andRectangle, mainX, flipY, origin] at *; omega

private theorem upper_flip_strip (hw : 2 ≤ w) :
    StripWalls ((GridIsometry.transpose I.width I.height).board I.board)
      (g.flipY-w-1) (g.flipY-3) g.mainX := by
  constructor
  · intro p hx hy hy'
    obtain ⟨q, rfl⟩ := (GridIsometry.transpose I.width I.height).cells.surjective p
    apply (GridIsometry.mem_walls _ _ _).mpr
    change q.1.val = g.mainX+1 at hx
    change g.flipY-w-1 ≤ q.2.val at hy
    change q.2.val ≤ g.flipY-3 at hy'
    apply g.wall_rectangle 4 q
    all_goals simp [andRectangle, mainX, flipY, origin] at *; omega
  · intro p hx hy hy'
    obtain ⟨q, rfl⟩ := (GridIsometry.transpose I.width I.height).cells.surjective p
    apply (GridIsometry.mem_walls _ _ _).mpr
    change q.1.val+1 = g.mainX at hx
    change g.flipY-w-1 ≤ q.2.val at hy
    change q.2.val ≤ g.flipY-3 at hy'
    apply g.wall_rectangle 2 q
    all_goals simp [andRectangle, mainX, flipY, origin] at *; omega

private theorem lower_normal (bits : Gates.Signals) :
    (g.toThickGateGlyph.embedding.cells (andCell w bits.left bits.upper bits.right .middle)).2.val+1 < g.flipY ∨
      g.flipY+w-2+1 <
        (g.toThickGateGlyph.embedding.cells (andCell w bits.left bits.upper bits.right (.lower 0))).2.val := by
  cases bits.left <;>
    dsimp [ThickGateGlyph.embedding, GridEmbedding.translate, andCell, andPoint, flipY, origin] <;> omega

private theorem upper_normal (hw : 2 ≤ w) (bits : Gates.Signals) :
    (g.toThickGateGlyph.embedding.cells
      (andCell w bits.left bits.upper bits.right (.upper ⟨w+4, by omega⟩))).2.val+1 < g.flipY-w-1 ∨
      g.flipY-3+1 <
        (g.toThickGateGlyph.embedding.cells (andCell w bits.left bits.upper bits.right .middle)).2.val := by
  cases bits.left <;>
    dsimp [ThickGateGlyph.embedding, GridEmbedding.translate, andCell, andPoint, flipY, origin] <;> omega

/-- Arbitrary successful motion transmits H's upward threshold through I to the real J box. -/
theorem flip_signal (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered) (hw : 2 ≤ w) :
    (S.position (g.labels (.lower 0))).2.val ≤ g.flipY+w-1 →
      (S.position (g.labels (.upper ⟨w+4, by omega⟩))).2.val ≤ g.flipY-w-3 := by
  have htI := g.input_track .middle rfl
  have htH := g.input_track (.lower 0) rfl
  have htJ := g.input_track (.upper ⟨w+4, by omega⟩) rfl
  have hIH : (M.source (g.labels .middle)).2.val < (M.source (g.labels (.lower 0))).2.val := by
    rw [g.sources, g.sources]
    have ha := Bool.toNat_le g.initialSignals.left
    dsimp [gateCell, GridEmbedding.translate, andCell, andPoint, origin]
    omega
  have hJI : (M.source (g.labels (.upper ⟨w+4, by omega⟩))).2.val < (M.source (g.labels .middle)).2.val := by
    rw [g.sources, g.sources]
    have ha := Bool.toNat_le g.initialSignals.left
    dsimp [gateCell, GridEmbedding.translate, andCell, andPoint, origin]
    omega
  have hl := vertical_strip_good h cert ho A g.flipY (g.flipY+w-2) g.mainX
    (g.labels .middle) (g.labels (.lower 0)) (g.lower_flip_strip hw) htI htH hIH
    (by rw [g.sources, g.sources]; exact g.lower_normal g.initialSignals)
    (by rw [g.targets, g.targets]; exact g.lower_normal g.targetSignals)
  have hr := vertical_strip_good h cert ho A (g.flipY-w-1) (g.flipY-3) g.mainX
    (g.labels (.upper ⟨w+4, by omega⟩)) (g.labels .middle) (g.upper_flip_strip hw) htJ htI hJI
    (by rw [g.sources, g.sources]; exact g.upper_normal hw g.initialSignals)
    (by rw [g.targets, g.targets]; exact g.upper_normal hw g.targetSignals)
  have hf : w+3 ≤ g.flipY := by unfold flipY origin; omega
  omega

end PushPuzzle.PushS.FiniteGateReadout.AndGlyph
