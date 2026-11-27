/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Soundness.Ambient

/-! The actual AND/OR conditions along all successful physical trajectories of placed long-wall gates. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Gates.Soundness


open Wires.Soundness

variable {I : Instance} {Label : Type} [Fintype Label]

/-- Translate the three literal trigger coordinates, retaining the specified full ambient state. -/
def translatedConfiguration {W H : ℕ} (dx dy : ℕ) (hx : dx+81 ≤ W) (hy : dy+107 ≤ H)
    (s : State W H) (kind : Bool) (bits : Signals) : AND.Configuration W H :=
  let e := GridEmbedding.translate dx dy hx hy
  ⟨s,e.cells (position kind bits (triggerA kind)),e.cells (position kind bits (triggerB kind)),
    e.cells (position kind bits (triggerC kind))⟩

private theorem and_good_translated {W H : ℕ} (dx dy : ℕ) (hx : dx+81 ≤ W) (hy : dy+107 ≤ H)
    (s : State W H) (bits : Signals) (hb : legal true bits) :
    AND.Good (dx+43) (dy+90) (translatedConfiguration dx dy hx hy s true bits) := by
  have hg := (legal_iff_and_good bits).mp hb
  change (position true bits (triggerC true)).1.val ≤ 43+3 →
    (position true bits (triggerA true)).1.val < 43 ∧ (position true bits (triggerB true)).2.val+1 < 90 at hg
  intro hc
  change dx+(position true bits (triggerC true)).1.val ≤ dx+43+3 at hc
  obtain ⟨ha,hb⟩ := hg (by omega)
  change dx+(position true bits (triggerA true)).1.val < dx+43 ∧
    dy+(position true bits (triggerB true)).2.val+1 < dy+90
  omega

private theorem or_good_translated {W H : ℕ} (dx dy : ℕ) (hx : dx+81 ≤ W) (hy : dy+107 ≤ H)
    (s : State W H) (bits : Signals) (hb : legal false bits) :
    OR.Good (dx+44) (dy+90) (translatedConfiguration dx dy hx hy s false bits) := by
  have hg := (legal_iff_or_good bits).mp hb
  change (position false bits (triggerC false)).1.val ≤ 44+3 →
    (position false bits (triggerA false)).1.val+1 < 44 ∨ (position false bits (triggerB false)).2.val+1 < 90 at hg
  intro hc
  change dx+(position false bits (triggerC false)).1.val ≤ dx+44+3 at hc
  have hh := hg (by omega)
  change dx+(position false bits (triggerA false)).1.val+1 < dx+44 ∨
    dy+(position false bits (triggerB false)).2.val+1 < dy+90
  omega

namespace GateGlyph

variable {M : SlotMatching I Label} {A : AxisTracks I} {kind : Bool}
    (g : GateGlyph M A kind) {S final : LabelledState Label I.width I.height}

private theorem source_configuration : g.configuration M.initialLabelled =
    translatedConfiguration g.dx g.dy g.fit_x g.fit_y I.initial kind g.initialSignals := by
  change AND.Configuration.mk I.initial (M.source (g.labels (triggerA kind)))
    (M.source (g.labels (triggerB kind))) (M.source (g.labels (triggerC kind))) = _
  rw [g.sources,g.sources,g.sources]
  rfl

private theorem target_configuration (ht : final.position = M.target) : g.configuration final =
    translatedConfiguration g.dx g.dy g.fit_x g.fit_y final.state kind g.targetSignals := by
  change AND.Configuration.mk final.state (final.position g.a) (final.position g.b) (final.position g.c) = _
  rw [ht]
  change AND.Configuration.mk final.state (M.target (g.labels (triggerA kind)))
    (M.target (g.labels (triggerB kind))) (M.target (g.labels (triggerC kind))) = _
  rw [g.targets,g.targets,g.targets]
  rfl

end GateGlyph

namespace GateGlyph

variable {M : SlotMatching I Label} {A : AxisTracks I} {S final : LabelledState Label I.width I.height}

/-- Every intermediate state of an arbitrary real successful AND trajectory satisfies AND legality. -/
theorem and_good (g : GateGlyph M A true) (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hstart : legal true g.initialSignals) (hfinish : legal true g.targetSignals) :
    AND.Good (g.dx+43) (g.dy+90) (g.configuration S) := by
  have hstep U V (hu : Successful M U final) (hv : Successful M V final)
      (hs : LabelledState.Step I.board U V) :
      AND.GeometricStep I.board (g.dx+43) (g.dy+90) (g.configuration U) (g.configuration V) :=
    ⟨g.and_shape hu cert,g.and_shape hv cert,hs.triple g.a g.b g.c⟩
  have hb := map_successful g.configuration h.before .refl h.after h.solved hstep
  have ha := map_successful g.configuration h.after h.before .refl h.solved hstep
  have hg0 : AND.Good (g.dx+43) (g.dy+90) (g.configuration M.initialLabelled) := by
    rw [g.source_configuration]
    exact and_good_translated _ _ _ _ _ _ hstart
  have hg1 : AND.Good (g.dx+43) (g.dy+90) (g.configuration final) := by
    rw [g.target_configuration (h.target ho cert)]
    exact and_good_translated _ _ _ _ _ _ hfinish
  exact AND.good_on_successful_path g.cavity_walls hg0 hg1 hb ha

/-- OR's target-A bound is derived from its prescribed real goal slot and the recovered physical identity. -/
theorem or_good (g : GateGlyph M A false) (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hstart : legal false g.initialSignals) (hfinish : legal false g.targetSignals) :
    OR.Good (g.dx+44) (g.dy+90) (g.configuration S) := by
  have hstep U V (hu : Successful M U final) (hv : Successful M V final)
      (hs : LabelledState.Step I.board U V) :
      OR.GeometricStep I.board (g.dx+44) (g.dy+90) (g.configuration U) (g.configuration V) :=
    ⟨g.common_shape hu,g.common_shape hv,hs.triple g.a g.b g.c⟩
  have hb := map_successful g.configuration h.before .refl h.after h.solved hstep
  have ha := map_successful g.configuration h.after h.before .refl h.solved hstep
  have hg0 : OR.Good (g.dx+44) (g.dy+90) (g.configuration M.initialLabelled) := by
    rw [g.source_configuration]
    exact or_good_translated _ _ _ _ _ _ hstart
  have hg1 : OR.Good (g.dx+44) (g.dy+90) (g.configuration final) := by
    rw [g.target_configuration (h.target ho cert)]
    exact or_good_translated _ _ _ _ _ _ hfinish
  have hA : (g.configuration final).a.1.val < g.dx+44 := by
    rw [g.target_configuration (h.target ho cert)]
    change g.dx+(position false g.targetSignals (triggerA false)).1.val < g.dx+44
    have hh : (position false g.targetSignals (triggerA false)).1.val < 44 := by
      rw [position_triggerA]
      split <;> decide
    exact Nat.add_lt_add_left hh _
  exact OR.good_on_successful_path g.cavity_walls hg0 hg1 hA hb ha

/-- Decode the three actual trigger thresholds, allowing every noncanonical intermediate position. -/
def decode {kind : Bool} (g : GateGlyph M A kind) (S : LabelledState Label I.width I.height) : Signals :=
  if kind then
    ⟨decide ((S.position g.a).1.val < g.dx+43),decide ((S.position g.b).2.val+1 < g.dy+90),
      decide ((S.position g.c).1.val ≤ g.dx+43+3)⟩
  else
    ⟨decide ((S.position g.a).1.val+1 < g.dx+44),decide ((S.position g.b).2.val+1 < g.dy+90),
      decide ((S.position g.c).1.val ≤ g.dx+44+3)⟩

/-- Actual successful motion decodes to a legal NCL gate state at every point. -/
theorem decode_legal {kind : Bool} (g : GateGlyph M A kind) (h : Successful M S final)
    (cert : Certificate I) (ho : M.Ordered)
    (hstart : legal kind g.initialSignals) (hfinish : legal kind g.targetSignals) : legal kind (g.decode S) := by
  cases kind
  · have hh := g.or_good h cert ho hstart hfinish
    simpa [legal,decode,OR.Good,configuration,LabelledState.triple] using hh
  · have hh := g.and_good h cert ho hstart hfinish
    simpa [legal,decode,AND.Good,configuration,LabelledState.triple] using hh

end GateGlyph
end PushPuzzle.PushFS.Gadgets.Gates.Soundness
