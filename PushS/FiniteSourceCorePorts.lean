/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceCoreGlyph
public import PushS.FiniteSourceArmEndpoints
public import PushS.FiniteSourceOrder
public import PushS.FiniteGateBoundary
public import PushS.FiniteRoutingRelay

public import PushS.FiniteGeometrySimp

/-! Actual outer core claims use exactly the adjoining arm's literal phase-one port slots. -/

public section
namespace PushPuzzle.PushS

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateReadout
open PushFS.Gadgets PushFS.Gadgets.Wires.Soundness
open scoped Classical

namespace FiniteGateReadout

variable {I : PushFS.Instance} {Label : Type} [Fintype Label]
    {M : SlotMatching I Label} {A : AxisTracks I} {w : ℕ}

namespace AndGlyph

/-- The actual outer normal slot and direction of one canonical core port. -/
@[expose] def port (g : AndGlyph M A w) (role : Fin 3) : PhysicalPort (I := I) (GlobalLabel := Label) where
  label := g.labels (andPortLabel w role)
  slot := g.toThickGateGlyph.embedding.cells (andCell w true true false (andPortLabel w role))
  direction := PortAnnulus.innerDirection role

attribute [local finite_gate_readout_coords]
  port PhysicalPort.High PortHigh Outward coordinates PortAnnulus.innerDirection andPortLabel ThickGateGlyph.embedding GridEmbedding.translate andCell andPoint outerA outerB outerC

private theorem port_claim (g : AndGlyph M A w) (S : LabelledState Label I.width I.height) (role : Fin 3) :
    decide ((g.port role).High S) =
      portInflow (g.boundarySignals S).left (g.boundarySignals S).upper (g.boundarySignals S).right role := by
  fin_cases role
  · change decide ((g.port 0).High S) = decide ((S.position g.outerA).1.val ≤ g.dx+(origin w-8*w-17))
    apply decide_eq_decide.mpr
    dsimp [finite_gate_readout_coords]
    unfold origin; omega
  · change decide ((g.port 1).High S) = decide ((S.position g.outerB).2.val ≤ g.dy+(origin w-8*w-32))
    apply decide_eq_decide.mpr
    dsimp [finite_gate_readout_coords]
    unfold origin; omega
  · apply Bool.eq_iff_iff.mpr
    change decide ((g.port 2).High S) = true ↔ !(decide ((S.position g.outerC).1.val < g.dx+origin w+3*w+13)) = true
    simp only [decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not]
    dsimp [finite_gate_readout_coords]
    omega

end AndGlyph

namespace OrGlyph

/-- The actual outer normal slot and direction of one canonical core port. -/
@[expose] def port (g : OrGlyph M A w) (role : Fin 3) : PhysicalPort (I := I) (GlobalLabel := Label) where
  label := g.labels (orPortLabel w role)
  slot := g.toThickGateGlyph.embedding.cells (orCell w true true false (orPortLabel w role))
  direction := PortAnnulus.innerDirection role

attribute [local finite_gate_readout_coords]
  port PhysicalPort.High PortHigh Outward coordinates PortAnnulus.innerDirection orPortLabel ThickGateGlyph.embedding GridEmbedding.translate orCell orPoint outerA outerB outerC

private theorem port_claim (g : OrGlyph M A w) (S : LabelledState Label I.width I.height) (role : Fin 3) :
    decide ((g.port role).High S) =
      portInflow (g.boundarySignals S).left (g.boundarySignals S).upper (g.boundarySignals S).right role := by
  fin_cases role
  · change decide ((g.port 0).High S) = decide ((S.position g.outerA).1.val ≤ g.dx+(origin w-2*w-8))
    apply decide_eq_decide.mpr
    dsimp [finite_gate_readout_coords]
    unfold origin; omega
  · change decide ((g.port 1).High S) = decide ((S.position g.outerB).2.val ≤ g.dy+(origin w-2*w-14))
    apply decide_eq_decide.mpr
    dsimp [finite_gate_readout_coords]
    unfold origin; omega
  · apply Bool.eq_iff_iff.mpr
    change decide ((g.port 2).High S) = true ↔ !(decide ((S.position g.outerC).1.val < g.dx+origin w+3*w+14)) = true
    simp only [decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not]
    dsimp [finite_gate_readout_coords]
    omega

end OrGlyph
end FiniteGateReadout

namespace FiniteSourceInventory.CoreSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : CoreSite w hw v)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])

/-- The three canonical claims read from the actual placed core. -/
@[expose] noncomputable def boundarySignals (S : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)) : Gates.Signals :=
  if h : s.gate.core.isAND = true then (s.andGlyph h hP hT).boundarySignals S
  else (s.orGlyph (Bool.eq_false_iff.mpr h) hP hT).boundarySignals S

/-- The actual outer normal slot and direction of one canonical core port. -/
@[expose] noncomputable def port (role : Fin 3) :
    PhysicalPort (I := checkedPuzzle w hw v hP hT) (GlobalLabel := (inventory w hw v).PhysicalLabel) :=
  if h : s.gate.core.isAND = true then (s.andGlyph h hP hT).port role
  else (s.orGlyph (Bool.eq_false_iff.mpr h) hP hT).port role

theorem port_label (role : Fin 3) : (s.port hP hT role).label = s.portLabel role := by
  unfold port portLabel
  split_ifs <;> rfl

theorem port_claim (S : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)) (role : Fin 3) :
    decide ((s.port hP hT role).High S) = portInflow (s.boundarySignals hP hT S).left
      (s.boundarySignals hP hT S).upper (s.boundarySignals hP hT S).right role := by
  unfold port boundarySignals
  split_ifs with hg
  · exact AndGlyph.port_claim (s.andGlyph hg hP hT) S role
  · exact OrGlyph.port_claim (s.orGlyph (Bool.eq_false_iff.mpr hg) hP hT) S role

theorem boundary_legal {S final : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)}
    (h : Successful (slotMatching w hw v hP hT) S final)
    (hs : Gates.legal s.gate.core.isAND s.gate.core.initial)
    (ht : Gates.legal s.gate.core.isAND s.gate.core.target) :
    Gates.legal s.gate.core.isAND (s.boundarySignals hP hT S) := by
  unfold boundarySignals
  split_ifs with hg
  · rw [hg] at hs ht ⊢
    exact (s.andGlyph hg hP hT).boundary_legal h (certificate w hw v hP hT) (ordered w hw v hP hT) hw hs ht
  · have hg' := Bool.eq_false_iff.mpr hg
    rw [hg'] at hs ht ⊢
    exact (s.orGlyph hg' hP hT).boundary_legal h (certificate w hw v hP hT) (ordered w hw v hP hT) hw hs ht

end FiniteSourceInventory.CoreSite
end PushPuzzle.PushS
