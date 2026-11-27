/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingReadoutSlots
public import PushS.FiniteRoutingInitial

/-! Concrete normal high-slot thresholds, independent of routing direction and rectangle orientation. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Gadgets.Wires.Soundness PushFS.Gadgets.Wires.Polyline

/-- The actual box has reached or passed its literal phase-one slot along the named route direction. -/
def PortHigh {W H : ℕ} (d : Direction) (slot actual : Cell W H) : Prop :=
  Outward d (coordinates slot) (coordinates actual)

private theorem portHigh_orient {W H : ℕ} (o : RectOrientation) (d : Direction)
    (slot actual : Cell W H) :
    PortHigh (o.direction d) ((o.axis W H).geometry.cells slot) ((o.axis W H).geometry.cells actual) ↔
      PortHigh d slot actual := by
  have hsx := slot.1.isLt
  have hsy := slot.2.isLt
  have hax := actual.1.isLt
  have hay := actual.2.isLt
  change Outward (o.direction d)
    (((o.axis W H).geometry.cells slot).1.val,((o.axis W H).geometry.cells slot).2.val)
    (((o.axis W H).geometry.cells actual).1.val,((o.axis W H).geometry.cells actual).2.val) ↔ _
  rw [←o.point_cells,←o.point_cells]
  rcases o with ⟨swap,flipX,flipY⟩
  cases swap <;> cases flipX <;> cases flipY <;> cases d <;>
    dsimp [PortHigh,Outward,coordinates,RectOrientation.point,RectOrientation.width,RectOrientation.height,
      RectOrientation.direction,RectOrientation.axis,AxisIsometry.refl,AxisIsometry.transpose,
      AxisIsometry.reflectX,AxisIsometry.reflectY,AxisIsometry.trans,
      GridIsometry.refl,GridIsometry.transpose,GridIsometry.reflectX,GridIsometry.reflectY,
      GridIsometry.reflectDirection,GridIsometry.transposeDirection,GridIsometry.trans] <;> omega

variable {I : PushFS.Instance} {GlobalLabel : Type} [Fintype GlobalLabel]
    {M : SlotMatching I GlobalLabel} {A : ComponentTracks I}
    {S final : LabelledState GlobalLabel I.width I.height}

namespace Line.Readout.LineGlyph

def inputHighSlot {w : ℕ} {above : Bool} (length : ℕ) (switch : Bool)
    (g : Line.Readout.LineGlyph M A w (Line.program w length switch) above) : Cell I.width I.height :=
  g.embedding.cells (Line.cell w g.hw _ true (Line.cutFirstLabel w _))

def outputHighSlot {w : ℕ} {above : Bool} (length : ℕ) (switch : Bool)
    (g : Line.Readout.LineGlyph M A w (Line.program w length switch) above) : Cell I.width I.height :=
  g.embedding.cells (Line.cell w g.hw _ true (Line.cutLastLabel w _))

private theorem port_signal {w : ℕ} {above : Bool} (length : ℕ) (switch : Bool)
    (g : Line.Readout.LineGlyph M A w (Line.program w length switch) above)
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : PortHigh .east (g.inputHighSlot length switch) (S.position (g.labels (Line.cutFirstLabel w _)))) :
    PortHigh .east (g.outputHighSlot length switch) (S.position (g.labels (Line.cutLastLabel w _))) := by
  dsimp [PortHigh,Outward,coordinates,inputHighSlot,embedding,GridEmbedding.translate,Line.cell] at hin
  rw [Line.position_first] at hin
  simp only [Bool.toNat_true] at hin
  have hh := g.program_signal length switch h cert ho (by omega)
  dsimp [PortHigh,Outward,coordinates,outputHighSlot,embedding,GridEmbedding.translate,Line.cell]
  rw [Line.Terminal.last_position]
  simp only [Bool.toNat_true]
  omega

end Line.Readout.LineGlyph

namespace Turn.Readout.TurnGlyph

def inputHighSlot {w : ℕ} (g : Turn.Readout.TurnGlyph M A w) : Cell I.width I.height :=
  g.embedding.cells (Turn.cell w true 0)

def outputHighSlot {w : ℕ} (g : Turn.Readout.TurnGlyph M A w) : Cell I.width I.height :=
  g.embedding.cells (Turn.cell w true 1)

private theorem port_signal {w : ℕ} (g : Turn.Readout.TurnGlyph M A w)
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : PortHigh .east g.inputHighSlot (S.position (g.labels 0))) :
    PortHigh .south g.outputHighSlot (S.position (g.labels 1)) := by
  have hrad : 2 ≤ FiniteTools.radius w := by unfold FiniteTools.radius; omega
  dsimp [PortHigh,Outward,coordinates,inputHighSlot,embedding,GridEmbedding.translate,Turn.cell,Turn.label,
    FiniteTools.turnMixedCell,FiniteTools.turnMixedPoint] at hin
  have hh := g.signal h cert ho (by dsimp [x]; omega)
  dsimp [PortHigh,Outward,coordinates,outputHighSlot,embedding,GridEmbedding.translate,Turn.cell,Turn.label,
    FiniteTools.turnMixedCell,FiniteTools.turnMixedPoint]
  dsimp [y] at hh
  omega

end Turn.Readout.TurnGlyph

/-- A complete concrete line transmits its actual phase-one slot threshold in every global travel direction. -/
theorem oriented_line_port_signal (o : RectOrientation) (d : Direction) (hd : o.direction d = .east)
    (A : ComponentTracks ((o.axis I.width I.height).geometry.reorientInstance I))
    (w length : ℕ) (switch above : Bool)
    (g : Line.Readout.LineGlyph (M.reorient (o.axis I.width I.height).geometry) A w (Line.program w length switch) above)
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : PortHigh d ((o.axis I.width I.height).geometry.cells.symm (g.inputHighSlot length switch))
      (S.position (g.labels (Line.cutFirstLabel w _)))) :
    PortHigh d ((o.axis I.width I.height).geometry.cells.symm (g.outputHighSlot length switch))
      (S.position (g.labels (Line.cutLastLabel w _))) := by
  have hi := (portHigh_orient o d _ _).mpr hin
  rw [(o.axis I.width I.height).geometry.cells.apply_symm_apply (g.inputHighSlot length switch),hd] at hi
  have hh := g.port_signal length switch (orient_successful M h (o.axis I.width I.height).geometry)
    (cert.reorient M o) (ho.reorient o) hi
  have hr := (portHigh_orient o d ((o.axis I.width I.height).geometry.cells.symm (g.outputHighSlot length switch))
    (S.position (g.labels (Line.cutLastLabel w _)))).mp
  apply hr
  rw [(o.axis I.width I.height).geometry.cells.apply_symm_apply (g.outputHighSlot length switch),hd]
  exact hh

/-- The concrete F/G corner connects the two actual adjoining route directions. -/
theorem oriented_turn_port_signal (o : RectOrientation) (incoming outgoing : Direction)
    (hi : o.direction incoming = .east) (hout : o.direction outgoing = .south)
    (A : ComponentTracks ((o.axis I.width I.height).geometry.reorientInstance I))
    (w : ℕ) (g : Turn.Readout.TurnGlyph (M.reorient (o.axis I.width I.height).geometry) A w)
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : PortHigh incoming ((o.axis I.width I.height).geometry.cells.symm g.inputHighSlot) (S.position (g.labels 0))) :
    PortHigh outgoing ((o.axis I.width I.height).geometry.cells.symm g.outputHighSlot) (S.position (g.labels 1)) := by
  have hin' := (portHigh_orient o incoming _ _).mpr hin
  rw [(o.axis I.width I.height).geometry.cells.apply_symm_apply g.inputHighSlot,hi] at hin'
  have hh := g.port_signal (orient_successful M h (o.axis I.width I.height).geometry)
    (cert.reorient M o) (ho.reorient o) hin'
  apply (portHigh_orient o outgoing _ _).mp
  rw [(o.axis I.width I.height).geometry.cells.apply_symm_apply g.outputHighSlot,hout]
  exact hh

end PushPuzzle.PushS.FiniteRouting
