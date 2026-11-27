/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Gadgets.Wires.Soundness.ComponentTracks
public import PushS.FiniteRoutingTurns
public import PushFS.Gadgets.Gates.Soundness.Relay.Corners
public import PushFS.Gadgets.Gates.Soundness.Bounds

/-! The actual owned F/G labels transmit a threshold through the thick guarded routing turn. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Turn.Readout

open PushFS PushFS.Gadgets.Wires.Soundness PushFS.Gadgets.Wires.Polyline
open PushFS.Gadgets.Gates.Soundness.Relay
open FiniteTools (radius)

variable {I : PushFS.Instance} {GlobalLabel : Type} [Fintype GlobalLabel]

structure TurnGlyph (M : SlotMatching I GlobalLabel) (A : ComponentTracks I) (w : ℕ) where
  hw : 2 ≤ w
  dx : ℕ
  dy : ℕ
  fit_x : dx+FiniteTools.side w ≤ I.width
  fit_y : dy+FiniteTools.side w ≤ I.height
  initialPhase : Bool
  targetPhase : Bool
  labels : Fin 2 ↪ GlobalLabel
  sources : ∀ i, M.source (labels i) = (GridEmbedding.translate dx dy fit_x fit_y).cells (cell w initialPhase i)
  targets : ∀ i, M.target (labels i) = (GridEmbedding.translate dx dy fit_x fit_y).cells (cell w targetPhase i)
  horizontalTag : A.name (M.source (labels 0)) = .horizontal (dy+radius w)
  verticalTag : A.name (M.source (labels 1)) = .vertical (dx+radius w)
  cornerTag : A.name ((GridEmbedding.translate dx dy fit_x fit_y).cells (center w)) = .sink (dx+radius w) (dy+radius w)
  walls : ∀ p ∈ FiniteTools.turnWalls w, (GridEmbedding.translate dx dy fit_x fit_y).cells p ∈ I.board.walls

namespace TurnGlyph

variable {M : SlotMatching I GlobalLabel} {A : ComponentTracks I} {w : ℕ}
    (g : TurnGlyph M A w) {S final : LabelledState GlobalLabel I.width I.height}

def embedding : GridEmbedding (FiniteTools.side w) (FiniteTools.side w) I.width I.height :=
  GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y

def x : ℕ := g.dx+radius w
def y : ℕ := g.dy+radius w

private theorem bounds (h : Successful M S final) :
    (S.position (g.labels 0)).1.val < g.x ∧ g.y < (S.position (g.labels 1)).2.val := by
  have hf := h.below_barrier_component A true g.y (g.labels 0) g.horizontalTag (g.embedding.cells (center w))
    rfl (by unfold embedding; rw [g.cornerTag, g.horizontalTag]; exact AxisTrack.noConfusion)
    (by
      rw [g.sources]
      have hq := Bool.toNat_le g.initialPhase
      dsimp [coord, embedding, GridEmbedding.translate, x, cell, label, FiniteTools.turnMixedCell,
        FiniteTools.turnMixedPoint, radius, center, FiniteTools.turnNode, FiniteTools.turnNodePoint]
      omega)
  have hg := h.above_barrier_component A false g.x (g.labels 1) g.verticalTag (g.embedding.cells (center w))
    rfl (by unfold embedding; rw [g.cornerTag, g.verticalTag]; exact AxisTrack.noConfusion)
    (by
      rw [g.sources]
      dsimp [coord, embedding, GridEmbedding.translate, y, cell, label, FiniteTools.turnMixedCell,
        FiniteTools.turnMixedPoint, radius, center, FiniteTools.turnNode, FiniteTools.turnNodePoint]
      omega)
  exact ⟨hf,hg⟩

private theorem wall_rectangle (i : Fin 2) (p : Cell I.width I.height)
    (hx : g.dx+(FiniteTools.turnRectangle w i).x ≤ p.1.val)
    (hx' : p.1.val < g.dx+(FiniteTools.turnRectangle w i).x+(FiniteTools.turnRectangle w i).width)
    (hy : g.dy+(FiniteTools.turnRectangle w i).y ≤ p.2.val)
    (hy' : p.2.val < g.dy+(FiniteTools.turnRectangle w i).y+(FiniteTools.turnRectangle w i).height) : p ∈ I.board.walls := by
  have hf := g.fit_x
  have hf' := g.fit_y
  have hq : (FiniteTools.turnRectangle w i).x+(FiniteTools.turnRectangle w i).width ≤ FiniteTools.side w ∧
      (FiniteTools.turnRectangle w i).y+(FiniteTools.turnRectangle w i).height ≤ FiniteTools.side w := by
    fin_cases i <;> simp [FiniteTools.turnRectangle, FiniteTools.side, radius] <;> omega
  let q : Cell (FiniteTools.side w) (FiniteTools.side w) := (⟨p.1.val-g.dx,by omega⟩,⟨p.2.val-g.dy,by omega⟩)
  have he : g.embedding.cells q = p := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [embedding, GridEmbedding.translate,q] <;> omega
  apply he ▸ g.walls q
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, (FiniteGeometry.Rectangle.mem_cells _ _ _ _).mpr ?_⟩
  dsimp [q]
  omega

private theorem corner_walls :
    Corner.Walls ((GridIsometry.reflectX I.width I.height).board I.board) (I.width-(g.x+1)) g.y := by
  have hwidth : g.x+1 < I.width := by have := g.fit_x; unfold x FiniteTools.side radius at *; omega
  have hw := g.hw
  constructor
  · intro p hx hy
    obtain ⟨q,rfl⟩ := (GridIsometry.reflectX I.width I.height).cells.surjective p
    apply (GridIsometry.mem_walls _ _ _).mpr
    change I.width-(q.1.val+1) = I.width-(g.x+1) at hx
    change q.2.val+1 = g.y at hy
    have hqx := q.1.isLt
    have hxe : q.1.val = g.x := by omega
    apply g.wall_rectangle 0 q
    all_goals simp [FiniteTools.turnRectangle, x, y, radius] at *; omega
  · intro p hx hy
    obtain ⟨q,rfl⟩ := (GridIsometry.reflectX I.width I.height).cells.surjective p
    apply (GridIsometry.mem_walls _ _ _).mpr
    change I.width-(q.1.val+1)+1 = I.width-(g.x+1) at hx
    change q.2.val = g.y at hy
    have hqx := q.1.isLt
    have hxe : q.1.val = g.x+1 := by omega
    apply g.wall_rectangle 1 q
    all_goals simp [FiniteTools.turnRectangle, x, y, radius] at *; omega

/-- Successful paths keep the real corner open, including every noncanonical intermediate slot. -/
theorem signal (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : g.x ≤ (S.position (g.labels 0)).1.val+1) : g.y+2 ≤ (S.position (g.labels 1)).2.val := by
  let e := GridIsometry.reflectX I.width I.height
  let j := I.width-(g.x+1)
  have hwidth : g.x+1 < I.width := by have := g.fit_x; unfold x FiniteTools.side radius at *; omega
  have shape U (hu : Successful M U final) :
      Corner.Shape j g.y (pair (I:=e.reorientInstance I) (orientLabels e U) (g.labels 0) (g.labels 1)) := by
    have hrow := hu.line_component A true g.y (g.labels 0) g.horizontalTag
    have hcol := hu.line_component A false g.x (g.labels 1) g.verticalTag
    have hb := g.bounds hu
    have hqx := (U.position (g.labels 0)).1.isLt
    refine ⟨(orientLabels e U).position_mem _, (orientLabels e U).position_mem _, hrow, ?_, ?_, hb.2⟩
    · change j < I.width-((U.position (g.labels 0)).1.val+1)
      dsimp [j]
      omega
    · change I.width-((U.position (g.labels 1)).1.val+1) = j
      change (U.position (g.labels 1)).1.val = g.x at hcol
      rw [hcol]
  have normal (phase : Bool) :
      j+1 < (e.cells (g.embedding.cells (cell w phase 0))).1.val ∨
      g.y+1 < (e.cells (g.embedding.cells (cell w phase 1))).2.val := by
    have hf := g.fit_x
    unfold FiniteTools.side radius at hf
    change j+1 < I.width-(g.dx+(cell w phase 0).1.val+1) ∨ g.y+1 < g.dy+(cell w phase 1).2.val
    cases phase <;>
      dsimp [j,x,y,cell,label,FiniteTools.turnMixedCell,
        FiniteTools.turnMixedPoint, radius] <;> omega
  have hs := normal g.initialPhase
  have ht := normal g.targetPhase
  change _ < (e.cells ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (cell w g.initialPhase 0))).1.val ∨
    _ < (e.cells ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (cell w g.initialPhase 1))).2.val at hs
  rw [←g.sources,←g.sources] at hs
  change _ < (e.cells ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (cell w g.targetPhase 0))).1.val ∨
    _ < (e.cells ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (cell w g.targetPhase 1))).2.val at ht
  rw [←g.targets,←g.targets] at ht
  have hg := oriented_corner_good h cert ho e j g.y (g.labels 0) (g.labels 1) g.corner_walls shape hs ht
  change j+1 < I.width-((S.position (g.labels 0)).1.val+1) ∨ g.y+1 < (S.position (g.labels 1)).2.val at hg
  have hqx := (S.position (g.labels 0)).1.isLt
  dsimp [j] at hg
  omega

end TurnGlyph
end PushPuzzle.PushS.FiniteRouting.Turn.Readout
