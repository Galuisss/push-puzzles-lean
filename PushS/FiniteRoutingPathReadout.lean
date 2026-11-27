/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingRelay
public import PushS.FiniteRoutingSharedSlots

/-! Indexed actual path programs relay through literal shared source and phase-one slots. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Gadgets.Wires.Soundness

variable {I : PushFS.Instance} {GlobalLabel : Type} [Fintype GlobalLabel] {M : SlotMatching I GlobalLabel}

namespace LineHop

def inputSlot (p : LineHop M) (phase : Bool) : Cell I.width I.height :=
  (p.orientation.axis I.width I.height).geometry.cells.symm
    (p.glyph.embedding.cells (Line.cell p.w p.glyph.hw _ phase (Line.cutFirstLabel p.w _)))

def outputSlot (p : LineHop M) (phase : Bool) : Cell I.width I.height :=
  (p.orientation.axis I.width I.height).geometry.cells.symm
    (p.glyph.embedding.cells (Line.cell p.w p.glyph.hw _ phase (Line.cutLastLabel p.w _)))

private theorem source_input
    (p : LineHop M) : M.source p.input.label = p.inputSlot p.glyph.initialPhase := by
  apply (p.orientation.axis I.width I.height).geometry.cells.injective
  unfold inputSlot
  rw [(p.orientation.axis I.width I.height).geometry.cells.apply_symm_apply (p.glyph.embedding.cells (Line.cell p.w p.glyph.hw _ p.glyph.initialPhase (Line.cutFirstLabel p.w _)))]
  exact p.glyph.sources _

private theorem source_output
    (p : LineHop M) : M.source p.output.label = p.outputSlot p.glyph.initialPhase := by
  apply (p.orientation.axis I.width I.height).geometry.cells.injective
  unfold outputSlot
  rw [(p.orientation.axis I.width I.height).geometry.cells.apply_symm_apply (p.glyph.embedding.cells (Line.cell p.w p.glyph.hw _ p.glyph.initialPhase (Line.cutLastLabel p.w _)))]
  exact p.glyph.sources _

end LineHop

namespace TurnHop

def inputSlot (p : TurnHop M) (phase : Bool) : Cell I.width I.height :=
  (p.orientation.axis I.width I.height).geometry.cells.symm (p.glyph.embedding.cells (Turn.cell p.w phase 0))

def outputSlot (p : TurnHop M) (phase : Bool) : Cell I.width I.height :=
  (p.orientation.axis I.width I.height).geometry.cells.symm (p.glyph.embedding.cells (Turn.cell p.w phase 1))

private theorem source_input
    (p : TurnHop M) : M.source p.input.label = p.inputSlot p.glyph.initialPhase := by
  apply (p.orientation.axis I.width I.height).geometry.cells.injective
  unfold inputSlot
  rw [(p.orientation.axis I.width I.height).geometry.cells.apply_symm_apply (p.glyph.embedding.cells (Turn.cell p.w p.glyph.initialPhase 0))]
  exact p.glyph.sources 0

private theorem source_output
    (p : TurnHop M) : M.source p.output.label = p.outputSlot p.glyph.initialPhase := by
  apply (p.orientation.axis I.width I.height).geometry.cells.injective
  unfold outputSlot
  rw [(p.orientation.axis I.width I.height).geometry.cells.apply_symm_apply (p.glyph.embedding.cells (Turn.cell p.w p.glyph.initialPhase 1))]
  exact p.glyph.sources 1

end TurnHop

def shiftPoint (dx dy : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (dx+p.1,dy+p.2)

/-- Every indexed instruction keeps its real code direction and all literal normal endpoint slots. -/
structure PathGlyph (M : SlotMatching I GlobalLabel) (w : ℕ) (hw : 2 ≤ w) (P : PathSpec) where
  dx : ℕ
  dy : ℕ
  line : Fin P.segments.length → LineHop M
  line_initial : ∀ i, (line i).glyph.initialPhase = P.initial
  line_direction : ∀ i, (line i).direction = segmentDirection (P.line i.val).segment
  line_input_slot : ∀ i phase, coordinates ((line i).inputSlot phase) = shiftPoint dx dy ((P.line i.val).firstWorld w hw phase)
  line_output_slot : ∀ i phase, coordinates ((line i).outputSlot phase) = shiftPoint dx dy ((P.line i.val).lastWorld w hw phase)
  turn : ∀ i : Fin P.segments.length, P.hasTurn i.val → TurnHop M
  turn_initial : ∀ i hi, (turn i hi).glyph.initialPhase = P.initial
  turn_incoming : ∀ i hi, (turn i hi).incoming = (P.turn i.val).incoming
  turn_outgoing : ∀ i hi, (turn i hi).outgoing = (P.turn i.val).outgoing
  turn_input_slot : ∀ i hi phase, coordinates ((turn i hi).inputSlot phase) = shiftPoint dx dy ((P.turn i.val).worldSlot w hw phase 0)
  turn_output_slot : ∀ i hi phase, coordinates ((turn i hi).outputSlot phase) = shiftPoint dx dy ((P.turn i.val).worldSlot w hw phase 1)

private theorem cell_of_coordinates {W H : ℕ} {p q : Cell W H} (he : coordinates p = coordinates q) : p = q :=
  Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

private theorem port_ext (p q : PhysicalPort (I:=I) (GlobalLabel:=GlobalLabel))
    (hsource : coordinates (M.source p.label) = coordinates (M.source q.label))
    (hslot : coordinates p.slot = coordinates q.slot) (hd : p.direction = q.direction) : p = q := by
  have hl := M.source.injective (cell_of_coordinates hsource)
  have hs := cell_of_coordinates hslot
  cases p
  cases q
  cases hl
  cases hs
  cases hd
  rfl

namespace PathGlyph

variable {w : ℕ} {hw : 2 ≤ w} {P : PathSpec} (g : PathGlyph M w hw P)

theorem line_source_input (i : Fin P.segments.length) :
    coordinates (M.source (g.line i).input.label) = shiftPoint g.dx g.dy ((P.line i.val).firstWorld w hw P.initial) := by
  rw [LineHop.source_input,g.line_initial]
  exact g.line_input_slot i P.initial

theorem line_source_output (i : Fin P.segments.length) :
    coordinates (M.source (g.line i).output.label) = shiftPoint g.dx g.dy ((P.line i.val).lastWorld w hw P.initial) := by
  rw [LineHop.source_output,g.line_initial]
  exact g.line_output_slot i P.initial

private theorem turn_source_input (i : Fin P.segments.length) (hi : P.hasTurn i.val) :
    coordinates (M.source (g.turn i hi).input.label) = shiftPoint g.dx g.dy ((P.turn i.val).worldSlot w hw P.initial 0) := by
  rw [TurnHop.source_input,g.turn_initial]
  exact g.turn_input_slot i hi P.initial

private theorem turn_source_output (i : Fin P.segments.length) (hi : P.hasTurn i.val) :
    coordinates (M.source (g.turn i hi).output.label) = shiftPoint g.dx g.dy ((P.turn i.val).worldSlot w hw P.initial 1) := by
  rw [TurnHop.source_output,g.turn_initial]
  exact g.turn_output_slot i hi P.initial

/-- Both source cells identify one shared physical F; both literal high cells identify its readout threshold. -/
private theorem incoming_seam (G : P.Geometry w) (i : Fin P.segments.length)
    (hi : P.hasTurn i.val) :
    (g.line i).output = (g.turn i hi).input := by
  have H := P.junction_contract w G i.val hi
  apply port_ext
  · rw [g.line_source_output,g.turn_source_input,H.incoming_shared_phase w hw _ _ _ P.initial]
  · change coordinates ((g.line i).outputSlot true) = coordinates ((g.turn i hi).inputSlot true)
    rw [g.line_output_slot,g.turn_input_slot,H.incoming_shared_phase w hw _ _ _ true]
  · change (g.line i).direction = (g.turn i hi).incoming
    rw [g.line_direction,g.turn_incoming]
    exact H.incoming_direction

private theorem outgoing_seam (G : P.Geometry w) (i : Fin P.segments.length)
    (hi : P.hasTurn i.val) :
    (g.turn i hi).output = (g.line ⟨i.val+1,hi.1⟩).input := by
  have H := P.junction_contract w G i.val hi
  apply port_ext
  · rw [g.turn_source_output,g.line_source_input,H.outgoing_shared_phase w hw _ _ _ P.initial]
  · change coordinates ((g.turn i hi).outputSlot true) = coordinates ((g.line ⟨i.val+1,hi.1⟩).inputSlot true)
    rw [g.turn_output_slot,g.line_input_slot,H.outgoing_shared_phase w hw _ _ _ true]
  · change (g.turn i hi).outgoing = (g.line ⟨i.val+1,hi.1⟩).direction
    rw [g.line_direction,g.turn_outgoing]
    exact H.outgoing_direction.symm

private theorem collinear_seam (G : P.Geometry w) (i : Fin P.segments.length)
    (hi : i.val+1 < P.segments.length) (hn : ¬P.hasTurn i.val) :
    (g.line i).output = (g.line ⟨i.val+1,hi⟩).input := by
  have H := P.collinear_contract w G i.val hi hn
  apply port_ext
  · rw [g.line_source_output,g.line_source_input,H.shared w hw _ _ P.initial]
  · change coordinates ((g.line i).outputSlot true) = coordinates ((g.line ⟨i.val+1,hi⟩).inputSlot true)
    rw [g.line_output_slot,g.line_input_slot,H.shared w hw _ _ true]
  · change (g.line i).direction = (g.line ⟨i.val+1,hi⟩).direction
    rw [g.line_direction,g.line_direction]
    exact H.directions

/-- The actual indexed path propagates from its first line through every real turn and final endpoint. -/
theorem signal (G : P.Geometry w) (hne : 0 < P.segments.length)
    {S final : LabelledState GlobalLabel I.width I.height}
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : (g.line ⟨0,hne⟩).input.High S) (i : Fin P.segments.length) : (g.line i).output.High S := by
  have aux (j : ℕ) (hj : j < P.segments.length) : (g.line ⟨j,hj⟩).output.High S := by
    induction j with
    | zero => exact (g.line _).signal h cert ho hin
    | succ j ih =>
      have hj' : j < P.segments.length := by omega
      have hprev := ih hj'
      by_cases ht : P.hasTurn j
      · have hturn : (g.turn ⟨j,hj'⟩ ht).input.High S := (g.incoming_seam G ⟨j,hj'⟩ ht) ▸ hprev
        have hout := (g.turn ⟨j,hj'⟩ ht).signal h cert ho hturn
        have hnext : (g.line ⟨j+1,hj⟩).input.High S := (g.outgoing_seam G ⟨j,hj'⟩ ht) ▸ hout
        exact (g.line ⟨j+1,hj⟩).signal h cert ho hnext
      · have hnext : (g.line ⟨j+1,hj⟩).input.High S := (g.collinear_seam G ⟨j,hj'⟩ hj ht) ▸ hprev
        exact (g.line ⟨j+1,hj⟩).signal h cert ho hnext
  exact aux i.val i.isLt

end PathGlyph
end PushPuzzle.PushS.FiniteRouting
