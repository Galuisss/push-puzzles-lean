/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateTracks
public import PushS.FiniteCoreRails
public import PushS.FiniteCavityPlacement
public import PushFS.Gadgets.Gates.Soundness.Bounds

/-! Concrete thick-gate glyphs and trigger geometry along arbitrary successful physical paths. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateReadout

open PushFS PushFS.Gadgets FiniteGeometry FiniteGateCore FiniteGateTracks
open PushFS.Gadgets.Wires.Soundness

abbrev GateLabel (w : ℕ) : Bool → Type
  | true => AndLabel w
  | false => OrLabel w

instance (w : ℕ) (kind : Bool) : Fintype (GateLabel w kind) := by
  cases kind <;> infer_instance

def gateCell (w : ℕ) : (kind : Bool) → Gates.Signals → GateLabel w kind → Cell (side w) (side w)
  | true, bits => andCell w bits.left bits.upper bits.right
  | false, bits => orCell w bits.left bits.upper bits.right

def gateTrack (w : ℕ) : (kind : Bool) → GateLabel w kind → AxisTrack
  | true => andTrack w
  | false => orTrack w

def gateWalls (w : ℕ) : Bool → Finset (Cell (side w) (side w))
  | true => andWalls w
  | false => orWalls w

def junction (w : ℕ) (kind : Bool) : ℕ := origin w + if kind then 3 else 4

def rightBoundary (w : ℕ) (kind : Bool) : ℕ := origin w+w + if kind then 4 else 5

def aLabel (w : ℕ) : (kind : Bool) → GateLabel w kind
  | true => .triggerA
  | false => .triggerA

def bLabel (w : ℕ) : (kind : Bool) → GateLabel w kind
  | true => .branchB 0
  | false => .branchB 0

def cLabel (w : ℕ) : (kind : Bool) → GateLabel w kind
  | true => .branchC 0
  | false => .branchC 0

def junctionCell (w : ℕ) (kind : Bool) : Cell (side w) (side w) :=
  (⟨junction w kind, by unfold junction origin side; split <;> omega⟩,
   ⟨origin w, by unfold origin side; omega⟩)

def protectionCell (w : ℕ) : Cell (side w) (side w) :=
  (⟨origin w-6*w-9, by unfold origin side; omega⟩,
   ⟨origin w, by unfold origin side; omega⟩)

def upperCornerCell (w : ℕ) : Cell (side w) (side w) :=
  (⟨origin w-6*w-9, by unfold origin side; omega⟩,
   ⟨origin w-6*w-21, by unfold origin side; omega⟩)

variable {I : PushFS.Instance} {Label : Type} [Fintype Label]

/-- A real whole-board gate carries only static placement, source/target and axis data. -/
structure ThickGateGlyph (M : SlotMatching I Label) (A : AxisTracks I) (w : ℕ) (kind : Bool) where
  dx : ℕ
  dy : ℕ
  fit_x : dx+side w ≤ I.width
  fit_y : dy+side w ≤ I.height
  initialSignals : Gates.Signals
  targetSignals : Gates.Signals
  labels : GateLabel w kind ↪ Label
  walls : ∀ p, p ∈ gateWalls w kind →
    (GridEmbedding.translate dx dy fit_x fit_y).cells p ∈ I.board.walls
  sources : ∀ l, M.source (labels l) = (GridEmbedding.translate dx dy fit_x fit_y).cells
    (gateCell w kind initialSignals l)
  targets : ∀ l, M.target (labels l) = (GridEmbedding.translate dx dy fit_x fit_y).cells
    (gateCell w kind targetSignals l)
  tracks : ∀ l, A.name (M.source (labels l)) = AxisTrack.shift dx dy (gateTrack w kind l)
  junctionTag : A.name ((GridEmbedding.translate dx dy fit_x fit_y).cells (junctionCell w kind)) =
    .horizontal (dy+origin w)

/-- The protected AND corner and its literal finite floor channel. -/
structure AndGlyph (M : SlotMatching I Label) (A : AxisTracks I) (w : ℕ)
    extends ThickGateGlyph M A w true where
  protectedTag : A.name ((GridEmbedding.translate dx dy fit_x fit_y).cells (protectionCell w)) =
    .sink (dx+origin w-6*w-9) (dy+origin w)
  upperTag : A.name ((GridEmbedding.translate dx dy fit_x fit_y).cells (upperCornerCell w)) =
    .sink (dx+origin w-6*w-9) (dy+origin w-6*w-21)
  railFloor : ∀ r : FiniteCoreRails.AndRail, ∀ i,
    (GridEmbedding.translate dx dy fit_x fit_y).cells (r.cell w i) ∉ I.board.walls

attribute [local irreducible] side

namespace ThickGateGlyph

variable {M : SlotMatching I Label} {A : AxisTracks I} {w : ℕ} {kind : Bool}
    (g : ThickGateGlyph M A w kind) {S final : LabelledState Label I.width I.height}

def embedding : GridEmbedding (side w) (side w) I.width I.height :=
  GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y

def a : Label := g.labels (aLabel w kind)
def b : Label := g.labels (bLabel w kind)
def c : Label := g.labels (cLabel w kind)

def configuration (S : LabelledState Label I.width I.height) : AND.Configuration I.width I.height :=
  S.triple g.a g.b g.c

private theorem track_a : A.name (M.source g.a) = .horizontal (g.dy+origin w) := by
  change A.name (M.source (g.labels (aLabel w kind))) = _
  rw [g.tracks]
  cases kind <;> rfl

private theorem track_b : A.name (M.source g.b) = .vertical (g.dx+junction w kind) := by
  change A.name (M.source (g.labels (bLabel w kind))) = _
  rw [g.tracks]
  cases kind <;> rfl

private theorem track_c : A.name (M.source g.c) = .horizontal (g.dy+origin w) := by
  change A.name (M.source (g.labels (cLabel w kind))) = _
  rw [g.tracks]
  cases kind <;> rfl

private theorem source_order (hw : 2 ≤ w) : (M.source g.a).1.val < (M.source g.c).1.val := by
  change (M.source (g.labels (aLabel w kind))).1.val < (M.source (g.labels (cLabel w kind))).1.val
  rw [g.sources, g.sources]
  have ha := Bool.toNat_le g.initialSignals.left
  have hc := Bool.toNat_le g.initialSignals.right
  cases kind <;>
    dsimp [gateCell, aLabel, cLabel, GridEmbedding.translate, andCell, andPoint, orCell, orPoint, origin] <;> omega

private theorem b_above (h : Successful M S final) : (S.position g.b).2.val < g.dy+origin w := by
  have hne : A.name (g.embedding.cells (junctionCell w kind)) ≠ A.name (M.source g.b) := by
    unfold embedding
    rw [g.junctionTag, g.track_b]
    exact AxisTrack.noConfusion
  have hc : cross false (g.embedding.cells (junctionCell w kind)) = g.dx+junction w kind := rfl
  have hb : coord false (M.source g.b) < coord false (g.embedding.cells (junctionCell w kind)) := by
    change (M.source (g.labels (bLabel w kind))).2.val < _
    rw [g.sources]
    have ht := Bool.toNat_le g.initialSignals.upper
    cases kind <;>
      dsimp [gateCell, bLabel, coord, embedding, GridEmbedding.translate, junctionCell,
        andCell, andPoint, orCell, orPoint, origin] <;> omega
  exact h.below_barrier A false (g.dx+junction w kind) g.b g.track_b
    (g.embedding.cells (junctionCell w kind)) hc hne hb

/-- Actual row, column, order and upper-barrier facts give the common gate shape. -/
private theorem common_shape (h : Successful M S final) (hw : 2 ≤ w) :
    OR.Shape (g.dx+junction w kind) (g.dy+origin w) (g.configuration S) :=
  ⟨S.position_mem g.a, S.position_mem g.b, S.position_mem g.c,
    h.line A true _ g.a g.track_a, h.line A true _ g.c g.track_c,
    h.line A false _ g.b g.track_b, g.b_above h,
    h.order A true _ g.a g.c g.track_a g.track_c (g.source_order hw)⟩

private theorem cavity_walls (hw : 2 ≤ w) :
    FiniteCavity.Walls I.board (g.dx+junction w kind) (g.dx+rightBoundary w kind) (g.dy+origin w) := by
  cases kind
  · exact (orCavityWalls w hw ∅).translate
      (by unfold origin side; omega) (by unfold origin; omega)
      (by unfold origin side; omega) g.dx g.dy g.fit_x g.fit_y g.walls
  · exact (andCavityWalls w hw ∅).translate
      (by unfold origin side; omega) (by unfold origin; omega)
      (by unfold origin side; omega) g.dx g.dy g.fit_x g.fit_y g.walls

def normalConfiguration (state : State I.width I.height) (bits : Gates.Signals) :
    AND.Configuration I.width I.height :=
  ⟨state, g.embedding.cells (gateCell w kind bits (aLabel w kind)),
    g.embedding.cells (gateCell w kind bits (bLabel w kind)),
    g.embedding.cells (gateCell w kind bits (cLabel w kind))⟩

private theorem source_configuration :
    g.configuration M.initialLabelled = g.normalConfiguration I.initial g.initialSignals := by
  change AND.Configuration.mk I.initial (M.source (g.labels (aLabel w kind)))
    (M.source (g.labels (bLabel w kind))) (M.source (g.labels (cLabel w kind))) = _
  rw [g.sources, g.sources, g.sources]
  rfl

private theorem target_configuration (ht : final.position = M.target) :
    g.configuration final = g.normalConfiguration final.state g.targetSignals := by
  change AND.Configuration.mk final.state (final.position g.a) (final.position g.b) (final.position g.c) = _
  rw [ht]
  change AND.Configuration.mk final.state (M.target (g.labels (aLabel w kind)))
    (M.target (g.labels (bLabel w kind))) (M.target (g.labels (cLabel w kind))) = _
  rw [g.targets, g.targets, g.targets]
  rfl

end ThickGateGlyph

namespace ThickGateGlyph

variable {M : SlotMatching I Label} {A : AxisTracks I} {w : ℕ}

private theorem and_normal_good (g : ThickGateGlyph M A w true) (hw : 2 ≤ w)
    (state : State I.width I.height) (bits : Gates.Signals) (hbits : Gates.legal true bits) :
    FiniteCavity.AND.Good (g.dx+junction w true) (g.dx+rightBoundary w true) (g.dy+origin w)
      (g.normalConfiguration state bits) := by
  have hg := (andConfiguration_good_iff w hw bits.left bits.upper bits.right).mpr
    (by simpa [Gates.legal] using hbits)
  intro hc
  have hc' : (andCell w bits.left bits.upper bits.right (.branchC 0)).1.val ≤ rightBoundary w true := by
    change g.dx+(andCell w bits.left bits.upper bits.right (.branchC 0)).1.val ≤
      g.dx+rightBoundary w true at hc
    omega
  have hh := hg hc'
  change (andCell w bits.left bits.upper bits.right .triggerA).1.val < junction w true ∧
    (andCell w bits.left bits.upper bits.right (.branchB 0)).2.val+1 < origin w at hh
  change g.dx+(andCell w bits.left bits.upper bits.right .triggerA).1.val < g.dx+junction w true ∧
    g.dy+(andCell w bits.left bits.upper bits.right (.branchB 0)).2.val+1 < g.dy+origin w
  omega

private theorem or_normal_good (g : ThickGateGlyph M A w false) (hw : 2 ≤ w)
    (state : State I.width I.height) (bits : Gates.Signals) (hbits : Gates.legal false bits) :
    FiniteCavity.OR.Good (g.dx+junction w false) (g.dx+rightBoundary w false) (g.dy+origin w)
      (g.normalConfiguration state bits) := by
  have hg := (orConfiguration_good_iff w hw bits.left bits.upper bits.right).mpr
    (by simpa [Gates.legal] using hbits)
  intro hc
  have hc' : (orCell w bits.left bits.upper bits.right (.branchC 0)).1.val ≤ rightBoundary w false := by
    change g.dx+(orCell w bits.left bits.upper bits.right (.branchC 0)).1.val ≤
      g.dx+rightBoundary w false at hc
    omega
  have hh := hg hc'
  change (orCell w bits.left bits.upper bits.right .triggerA).1.val+1 < junction w false ∨
    (orCell w bits.left bits.upper bits.right (.branchB 0)).2.val+1 < origin w at hh
  change g.dx+(orCell w bits.left bits.upper bits.right .triggerA).1.val+1 < g.dx+junction w false ∨
    g.dy+(orCell w bits.left bits.upper bits.right (.branchB 0)).2.val+1 < g.dy+origin w
  omega

/-- The OR threshold follows from actual track conservation and both prescribed legal normal endpoints. -/
theorem or_good (g : ThickGateGlyph M A w false) (hw : 2 ≤ w)
    {S final : LabelledState Label I.width I.height} (h : Successful M S final)
    (cert : Certificate I) (ho : M.Ordered)
    (hstart : Gates.legal false g.initialSignals) (hfinish : Gates.legal false g.targetSignals) :
    FiniteCavity.OR.Good (g.dx+junction w false) (g.dx+rightBoundary w false) (g.dy+origin w)
      (g.configuration S) := by
  have hstep U V (hu : Successful M U final) (hv : Successful M V final)
      (hs : LabelledState.Step I.board U V) :
      FiniteCavity.OR.GeometricStep I.board (g.dx+junction w false) (g.dy+origin w)
        (g.configuration U) (g.configuration V) :=
    ⟨g.common_shape hu hw, g.common_shape hv hw, hs.triple g.a g.b g.c⟩
  have hb := map_successful g.configuration h.before .refl h.after h.solved hstep
  have ha := map_successful g.configuration h.after h.before .refl h.solved hstep
  have hg0 := g.or_normal_good hw I.initial g.initialSignals hstart
  have hg1 := g.or_normal_good hw final.state g.targetSignals hfinish
  rw [← g.source_configuration] at hg0
  rw [← g.target_configuration (h.target ho cert)] at hg1
  have hfinalA : (g.configuration final).a.1.val < g.dx+junction w false := by
    rw [g.target_configuration (h.target ho cert)]
    have ht := Bool.toNat_le g.targetSignals.left
    dsimp [normalConfiguration, embedding, gateCell, aLabel, GridEmbedding.translate,
      orCell, orPoint, junction, origin]
    omega
  exact FiniteCavity.OR.good_on_successful_path (g.cavity_walls hw) hg0 hg1 hfinalA hb ha

end ThickGateGlyph

namespace AndGlyph

variable {M : SlotMatching I Label} {A : AxisTracks I} {w : ℕ}
    (g : AndGlyph M A w) {S final : LabelledState Label I.width I.height}

def guard (i : Fin (3*w+5)) : Label := g.labels (.guard i)

def d : Label := g.guard ⟨3*w+4, by omega⟩

theorem track_guard (i : Fin (3*w+5)) :
    A.name (M.source (g.guard i)) = .horizontal (g.dy+origin w) := by
  change A.name (M.source (g.labels (.guard i))) = _
  rw [g.tracks]
  rfl

private theorem main_component (l m : AndLabel w)
    (hl : FiniteCoreRails.andRail l = .main) (hm : FiniteCoreRails.andRail m = .main) :
    component I.board (M.source (g.labels l)) = component I.board (M.source (g.labels m)) := by
  rw [g.sources, g.sources]
  apply component_eq_iff.mpr
  apply FiniteCoreRails.andCells_connected w
    g.initialSignals.left g.initialSignals.upper g.initialSignals.right l m (hl.trans hm.symm)
    g.toThickGateGlyph.embedding I.board
  intro i
  exact g.railFloor _ i

/-- The first guard box cannot cross the actual protection-corner sink. -/
theorem first_guard_lower (h : Successful M S final) :
    g.dx+(origin w-6*w-9)+1 ≤ (S.position (g.guard 0)).1.val := by
  have hne : A.name (g.toThickGateGlyph.embedding.cells (protectionCell w)) ≠
      A.name (M.source (g.guard 0)) := by
    unfold ThickGateGlyph.embedding
    rw [g.protectedTag, g.track_guard]
    exact AxisTrack.noConfusion
  have hc : cross true (g.toThickGateGlyph.embedding.cells (protectionCell w)) = g.dy+origin w := rfl
  have hs : coord true (g.toThickGateGlyph.embedding.cells (protectionCell w)) <
      coord true (M.source (g.guard 0)) := by
    change _ < (M.source (g.labels (.guard 0))).1.val
    rw [g.sources]
    have ha := Bool.toNat_le g.initialSignals.left
    dsimp [coord, ThickGateGlyph.embedding, GridEmbedding.translate, protectionCell,
      gateCell, andCell, andPoint, origin]
    omega
  have hh := h.above_barrier A true (g.dy+origin w) (g.guard 0) (g.track_guard 0)
    (g.toThickGateGlyph.embedding.cells (protectionCell w)) hc hne hs
  change g.dx+(origin w-6*w-9) < (S.position (g.guard 0)).1.val at hh
  omega

/-- Every physical guard interval retains its full empty-cell gap along a successful path. -/
private theorem guard_lower (h : Successful M S final) (cert : Certificate I) (i : Fin (3*w+5)) :
    g.dx+(origin w-6*w-9)+1+2*i.val ≤ (S.position (g.guard i)).1.val := by
  induction i using Fin.induction with
  | zero => simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] using g.first_guard_lower h
  | succ i ih =>
    have hord : coord true (M.source (g.guard i.castSucc)) < coord true (M.source (g.guard i.succ)) := by
      change (M.source (g.labels (.guard i.castSucc))).1.val < (M.source (g.labels (.guard i.succ))).1.val
      rw [g.sources, g.sources]
      have ha := Bool.toNat_le g.initialSignals.left
      dsimp [gateCell, GridEmbedding.translate, andCell, andPoint]
      have hi := i.isLt
      unfold origin
      omega
    have hg := h.gap cert A true (g.dy+origin w) (g.guard i.castSucc) (g.guard i.succ)
      (g.track_guard _) (g.track_guard _) (g.main_component (.guard _) (.guard _) rfl rfl) hord
    change (S.position (g.guard i.castSucc)).1.val+2 ≤ (S.position (g.guard i.succ)).1.val at hg
    simp only [Fin.val_succ, Fin.val_castSucc] at *
    omega

/-- The complete guard chain forces the genuine AND trigger to stay at or right of its lower bound. -/
private theorem a_lower (h : Successful M S final) (cert : Certificate I) :
    g.dx+junction w true ≤ (S.position g.toThickGateGlyph.a).1.val+1 := by
  have hd := g.guard_lower h cert ⟨3*w+4, by omega⟩
  have ho : coord true (M.source g.d) < coord true (M.source g.toThickGateGlyph.a) := by
    change (M.source (g.labels (.guard ⟨3*w+4, by omega⟩))).1.val <
      (M.source (g.labels .triggerA)).1.val
    rw [g.sources, g.sources]
    have ha := Bool.toNat_le g.initialSignals.left
    dsimp [gateCell, GridEmbedding.translate, andCell, andPoint]
    unfold origin
    omega
  have hg := h.gap cert A true (g.dy+origin w) g.d g.toThickGateGlyph.a
    (g.track_guard _) g.track_a (g.main_component (.guard _) .triggerA rfl rfl) ho
  change (S.position g.d).1.val+2 ≤ (S.position g.toThickGateGlyph.a).1.val at hg
  change g.dx+(origin w-6*w-9)+1+2*(3*w+4) ≤ (S.position g.d).1.val at hd
  dsimp [junction, origin] at *
  omega

/-- All AND shape fields are consequences of the successful physical path. -/
private theorem shape (h : Successful M S final) (cert : Certificate I) (hw : 2 ≤ w) :
    AND.Shape (g.dx+junction w true) (g.dy+origin w) (g.configuration S) := by
  have hs := g.common_shape h hw
  exact ⟨hs.a_box, hs.b_box, hs.c_box, hs.a_row, hs.c_row, hs.b_col, hs.b_above,
    g.a_lower h cert, hs.order⟩

/-- Thick AND contraction obeys its real input thresholds throughout every successful trajectory. -/
theorem good (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered) (hw : 2 ≤ w)
    (hstart : Gates.legal true g.initialSignals) (hfinish : Gates.legal true g.targetSignals) :
    FiniteCavity.AND.Good (g.dx+junction w true) (g.dx+rightBoundary w true) (g.dy+origin w)
      (g.configuration S) := by
  have hstep U V (hu : Successful M U final) (hv : Successful M V final)
      (hs : LabelledState.Step I.board U V) :
      FiniteCavity.AND.GeometricStep I.board (g.dx+junction w true) (g.dy+origin w)
        (g.configuration U) (g.configuration V) :=
    ⟨g.shape hu cert hw, g.shape hv cert hw, hs.triple g.a g.b g.c⟩
  have hb := map_successful g.toThickGateGlyph.configuration h.before .refl h.after h.solved hstep
  have ha := map_successful g.toThickGateGlyph.configuration h.after h.before .refl h.solved hstep
  have hg0 := g.and_normal_good hw I.initial g.initialSignals hstart
  have hg1 := g.and_normal_good hw final.state g.targetSignals hfinish
  rw [← g.source_configuration] at hg0
  rw [← g.target_configuration (h.target ho cert)] at hg1
  exact FiniteCavity.AND.good_on_successful_path (g.cavity_walls hw) hg0 hg1 hb ha

end AndGlyph
end PushPuzzle.PushS.FiniteGateReadout
