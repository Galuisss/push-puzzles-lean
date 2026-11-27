/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPortReadout

/-! Finite sequences of actual line and turn glyphs relay thresholds across their shared physical slots. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Gadgets.Wires.Soundness

variable {I : PushFS.Instance} {GlobalLabel : Type} [Fintype GlobalLabel]
    (M : SlotMatching I GlobalLabel)

/-- A port is an actual physical identity, its literal phase-one slot, and the route travel direction. -/
structure PhysicalPort where
  label : GlobalLabel
  slot : Cell I.width I.height
  direction : Direction

namespace PhysicalPort

def High (p : PhysicalPort (I:=I) (GlobalLabel:=GlobalLabel)) (S : LabelledState GlobalLabel I.width I.height) : Prop :=
  PortHigh p.direction p.slot (S.position p.label)

end PhysicalPort

/-- Static data of one whole emitted straight program on the actual reoriented board. -/
structure LineHop where
  orientation : RectOrientation
  direction : Direction
  aligned : orientation.direction direction = .east
  tracks : ComponentTracks ((orientation.axis I.width I.height).geometry.reorientInstance I)
  w : ℕ
  length : ℕ
  switch : Bool
  above : Bool
  glyph : Line.Readout.LineGlyph (M.reorient (orientation.axis I.width I.height).geometry)
    tracks w (Line.program w length switch) above

namespace LineHop

variable {M} (p : LineHop M)

def input : PhysicalPort (I:=I) (GlobalLabel:=GlobalLabel) :=
  ⟨p.glyph.labels (Line.cutFirstLabel p.w _),
    (p.orientation.axis I.width I.height).geometry.cells.symm (p.glyph.inputHighSlot p.length p.switch),p.direction⟩

def output : PhysicalPort (I:=I) (GlobalLabel:=GlobalLabel) :=
  ⟨p.glyph.labels (Line.cutLastLabel p.w _),
    (p.orientation.axis I.width I.height).geometry.cells.symm (p.glyph.outputHighSlot p.length p.switch),p.direction⟩

theorem signal {S final : LabelledState GlobalLabel I.width I.height}
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : p.input.High S) : p.output.High S :=
  oriented_line_port_signal p.orientation p.direction p.aligned p.tracks p.w p.length p.switch p.above p.glyph h cert ho hin

end LineHop

/-- Static data of one actual F/G turn, retaining both exact adjoining directions. -/
structure TurnHop where
  orientation : RectOrientation
  incoming : Direction
  outgoing : Direction
  incoming_aligned : orientation.direction incoming = .east
  outgoing_aligned : orientation.direction outgoing = .south
  tracks : ComponentTracks ((orientation.axis I.width I.height).geometry.reorientInstance I)
  w : ℕ
  glyph : Turn.Readout.TurnGlyph (M.reorient (orientation.axis I.width I.height).geometry) tracks w

namespace TurnHop

variable {M} (p : TurnHop M)

def input : PhysicalPort (I:=I) (GlobalLabel:=GlobalLabel) :=
  ⟨p.glyph.labels 0,(p.orientation.axis I.width I.height).geometry.cells.symm p.glyph.inputHighSlot,p.incoming⟩

def output : PhysicalPort (I:=I) (GlobalLabel:=GlobalLabel) :=
  ⟨p.glyph.labels 1,(p.orientation.axis I.width I.height).geometry.cells.symm p.glyph.outputHighSlot,p.outgoing⟩

theorem signal {S final : LabelledState GlobalLabel I.width I.height}
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : p.input.High S) : p.output.High S :=
  oriented_turn_port_signal p.orientation p.incoming p.outgoing p.incoming_aligned p.outgoing_aligned
    p.tracks p.w p.glyph h cert ho hin

end TurnHop

abbrev RelayHop := LineHop M ⊕ TurnHop M

namespace RelayHop

variable {M}

def input : RelayHop M → PhysicalPort (I:=I) (GlobalLabel:=GlobalLabel)
  | .inl p => p.input
  | .inr p => p.input

def output : RelayHop M → PhysicalPort (I:=I) (GlobalLabel:=GlobalLabel)
  | .inl p => p.output
  | .inr p => p.output

theorem signal (p : RelayHop M) {S final : LabelledState GlobalLabel I.width I.height}
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : p.input.High S) : p.output.High S := by
  cases p with
  | inl p => exact p.signal h cert ho hin
  | inr p => exact p.signal h cert ho hin

end RelayHop

end PushPuzzle.PushS.FiniteRouting
