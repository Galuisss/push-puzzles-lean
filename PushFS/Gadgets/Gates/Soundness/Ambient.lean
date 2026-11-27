/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Soundness.Bounds
public import PushFS.Gadgets.Gates.Soundness.Geometry

/-! Actual trigger geometry on arbitrary successful paths through a placed long-wall gate. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Gates.Soundness

open Wires.Soundness

variable {I : Instance} {Label : Type} [Fintype Label]

def junctionPoint (kind : Bool) : C := if kind then (43,90) else (44,90)
@[simp] theorem junctionPoint_x (kind : Bool) : (junctionPoint kind).1.val = junction kind := by cases kind <;> rfl
@[simp] theorem junctionPoint_y (kind : Bool) : (junctionPoint kind).2.val = 90 := by cases kind <;> rfl

/-- Pure static layout data: exact walls and physical slots, initial rail names and two named junction cells. -/
structure GateGlyph (M : SlotMatching I Label) (A : AxisTracks I) (kind : Bool) where
  dx : ℕ
  dy : ℕ
  fit_x : dx+81 ≤ I.width
  fit_y : dy+107 ≤ I.height
  initialSignals : Signals
  targetSignals : Signals
  labels : Fin (slots kind).length ↪ Label
  walls : (GridEmbedding.translate dx dy fit_x fit_y).WallsAgree (board kind ∅) I.board
  sources : ∀ i, M.source (labels i) = (GridEmbedding.translate dx dy fit_x fit_y).cells
    (position kind initialSignals i)
  targets : ∀ i, M.target (labels i) = (GridEmbedding.translate dx dy fit_x fit_y).cells
    (position kind targetSignals i)
  tracks : ∀ i, A.name (M.source (labels i)) = AxisTrack.shift dx dy (axisName kind (position kind initialSignals i))
  junctionTag : A.name ((GridEmbedding.translate dx dy fit_x fit_y).cells (junctionPoint kind)) = .horizontal (dy+90)
  protectedTag : kind=true → A.name ((GridEmbedding.translate dx dy fit_x fit_y).cells (39,90)) = .sink (dx+39) (dy+90)

namespace GateGlyph

variable {M : SlotMatching I Label} {A : AxisTracks I} {kind : Bool}
    (g : GateGlyph M A kind) {S final : LabelledState Label I.width I.height}

def a : Label := g.labels (triggerA kind)
def b : Label := g.labels (triggerB kind)
def c : Label := g.labels (triggerC kind)
def d : Label := g.labels (triggerD kind)

/-- Three actual trigger identities with the entire actual unlabelled state and player. -/
def configuration (S : LabelledState Label I.width I.height) : AND.Configuration I.width I.height := S.triple g.a g.b g.c

private theorem track_a : A.name (M.source g.a) = .horizontal (g.dy+90) := by
  change A.name (M.source (g.labels (triggerA kind))) = _
  rw [g.tracks,(trigger_axes kind g.initialSignals).1]
  rfl

private theorem track_b : A.name (M.source g.b) = .vertical (g.dx+junction kind) := by
  change A.name (M.source (g.labels (triggerB kind))) = _
  rw [g.tracks,(trigger_axes kind g.initialSignals).2.1]
  rfl

private theorem track_c : A.name (M.source g.c) = .horizontal (g.dy+90) := by
  change A.name (M.source (g.labels (triggerC kind))) = _
  rw [g.tracks,(trigger_axes kind g.initialSignals).2.2.1]
  rfl

private theorem source_order : (M.source g.a).1.val < (M.source g.c).1.val := by
  change (M.source (g.labels (triggerA kind))).1.val < (M.source (g.labels (triggerC kind))).1.val
  rw [g.sources,g.sources]
  exact Nat.add_lt_add_left (trigger_order kind g.initialSignals).1 _

/-- B stays above the real horizontal junction, by conservation of its vertical SCC. -/
private theorem b_above (h : Successful M S final) : (S.position g.b).2.val < g.dy+90 := by
  have hne : A.name ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (junctionPoint kind)) ≠
      A.name (M.source g.b) := by rw [g.junctionTag,g.track_b]; exact AxisTrack.noConfusion
  have hc : cross false ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (junctionPoint kind)) =
      g.dx+junction kind := by change g.dx+(junctionPoint kind).1.val=g.dx+junction kind; rw [junctionPoint_x]
  have hstart : coord false (M.source g.b) <
      coord false ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (junctionPoint kind)) := by
    change (M.source (g.labels (triggerB kind))).2.val < _
    rw [g.sources]
    change g.dy+(position kind g.initialSignals (triggerB kind)).2.val < g.dy+(junctionPoint kind).2.val
    rw [junctionPoint_y]
    exact Nat.add_lt_add_left (trigger_order kind g.initialSignals).2.1 _
  have hh := h.below_barrier A false (g.dx+junction kind) g.b g.track_b
    ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (junctionPoint kind)) hc hne hstart
  change (S.position g.b).2.val < g.dy+(junctionPoint kind).2.val at hh
  simpa only [junctionPoint_y] using hh

/-- Every common OR/AND trigger-shape fact is derived from the actual successful physical trajectory. -/
theorem common_shape (h : Successful M S final) :
    OR.Shape (g.dx+junction kind) (g.dy+90) (g.configuration S) :=
  ⟨S.position_mem g.a,S.position_mem g.b,S.position_mem g.c,
    h.line A true _ g.a g.track_a,h.line A true _ g.c g.track_c,
    h.line A false _ g.b g.track_b,g.b_above h,h.order A true _ g.a g.c g.track_a g.track_c g.source_order⟩

/-- The actual five-cell cavity wall stencil survives the whole-board placement. -/
theorem cavity_walls : AND.CavityWalls I.board (g.dx+junction kind) (g.dy+90) :=
  (Soundness.cavity_walls kind).translate (by cases kind <;> decide) (by decide) (by decide)
    g.dx g.dy g.fit_x g.fit_y g.walls

end GateGlyph

namespace GateGlyph

variable {M : SlotMatching I Label} {A : AxisTracks I} (g : GateGlyph M A true)
    {S final : LabelledState Label I.width I.height}

private theorem track_d : A.name (M.source g.d) = .horizontal (g.dy+90) := by
  change A.name (M.source (g.labels (triggerD true))) = _
  rw [g.tracks,(trigger_axes true g.initialSignals).2.2.2 rfl]
  rfl

/-- D cannot pass the real protected sink, and the actual D/A gap is at least two. -/
private theorem a_lower (h : Successful M S final) (cert : Certificate I) : g.dx+43 ≤
    (S.position g.a).1.val+1 := by
  have hne : A.name ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (39,90)) ≠ A.name (M.source g.d) := by
    rw [g.protectedTag rfl,g.track_d]
    exact AxisTrack.noConfusion
  have hstart : coord true ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (39,90)) <
      coord true (M.source g.d) := by
    change g.dx+39 < (M.source (g.labels (triggerD true))).1.val
    rw [g.sources]
    exact Nat.add_lt_add_left ((trigger_order true g.initialSignals).2.2 rfl).1 _
  have hd := h.above_barrier A true (g.dy+90) g.d g.track_d
    ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (39,90)) rfl hne hstart
  have hc : component I.board (M.source g.d) = component I.board (M.source g.a) := by
    change component I.board (M.source (g.labels (triggerD true))) = component I.board (M.source (g.labels (triggerA true)))
    rw [g.sources,g.sources]
    have hh := da_component g.initialSignals
    exact component_eq_iff.mpr ⟨GridEmbedding.staticReach g.walls hh.1,GridEmbedding.staticReach g.walls hh.2⟩
  have ho : (M.source g.d).1.val < (M.source g.a).1.val := by
    change (M.source (g.labels (triggerD true))).1.val < (M.source (g.labels (triggerA true))).1.val
    rw [g.sources,g.sources]
    exact Nat.add_lt_add_left ((trigger_order true g.initialSignals).2.2 rfl).2 _
  have hg := h.gap cert A true (g.dy+90) g.d g.a g.track_d g.track_a hc ho
  change g.dx+39 < (S.position g.d).1.val at hd
  change (S.position g.d).1.val+2 ≤ (S.position g.a).1.val at hg
  omega

/-- The AND shape, including its protected lower bound, is a derived property of actual success. -/
theorem and_shape (h : Successful M S final) (cert : Certificate I) :
    AND.Shape (g.dx+43) (g.dy+90) (g.configuration S) := by
  have hs := g.common_shape h
  exact ⟨hs.a_box,hs.b_box,hs.c_box,hs.a_row,hs.c_row,hs.b_col,hs.b_above,g.a_lower h cert,hs.order⟩

end GateGlyph
end PushPuzzle.PushFS.Gadgets.Gates.Soundness
