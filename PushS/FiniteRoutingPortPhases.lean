/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPortBounds
public import PushS.FiniteRoutingSpacing

/-! Phase-exact ownership bounds leave two cells between reciprocal canonical port inventories. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side

def PortPhaseBound (w : ℕ) (face : Direction) (incoming phase : Bool) (a : ℕ × ℕ) : Prop :=
  let b := boundarySlot w face incoming phase
  let gap := if incoming then 2 else 0
  match face with
  | .east => a.1+gap ≤ b.1
  | .south => a.2+gap ≤ b.2
  | .west => b.1+gap ≤ a.1
  | .north => b.2+gap ≤ a.2

private theorem line_finish_phase_bound (w : ℕ) (hw : 2 ≤ w) (c : LineCode)
    (hc : LineGood w c.segment)
    (face : Direction) (incoming : Bool) (hd : segmentDirection c.segment = face)
    (he : c.segment.finish = advance face.opposite (boundaryPoint w face) incoming.toNat)
    (hlast : c.last = !incoming) (goal : Bool) (l : (PrimitiveCode.line c).Labels w) :
    PortPhaseBound w face incoming (if goal then c.target else c.initial)
      ((PrimitiveCode.line c).actor w hw goal l) := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let phase := if goal then c.target else c.initial
  have hlen := Line.program_span_of_bound w _ (c.above != c.desiredSide) hc.2.1
  change Line.span w atoms = segmentLength c.segment at hlen
  have hp := Line.positions_bounds w hw phase atoms (Line.position_mem w atoms phase l.val)
  rw [hlen] at hp
  have hphase := Bool.toNat_le phase
  have hpos : Line.position w atoms phase l.val+(if incoming then 2 else 0) ≤ segmentLength c.segment+phase.toNat := by
    cases incoming
    · simpa using hp.2
    · have hl : c.last = false := hlast
      let l' : Line.OwnedLabel w atoms c.first false := ⟨l.val,by simpa only [hl] using l.property⟩
      have hb := Line.owned_position_before_last w hw atoms phase c.first l'
      change Line.position w atoms phase l.val+2 ≤ Line.span w atoms+phase.toNat at hb
      simpa only [hlen,↓reduceIte] using hb
  have ht := segment_travels c.segment hc.1
  rw [hd,he] at ht
  rw [line_actor w hw c hc goal l,hd]
  change PortPhaseBound w face incoming phase (Line.along w face c.segment.start (Line.position w atoms phase l.val))
  cases incoming <;> cases face <;>
    dsimp [PortPhaseBound,boundarySlot,Travels,advance,Line.along,Direction.opposite,boundaryPoint] at * <;>
    simp only [padding,tileStride,spacing] at * <;> omega

private theorem line_start_phase_bound (w : ℕ) (hw : 2 ≤ w) (c : LineCode)
    (hc : LineGood w c.segment)
    (face : Direction) (hd : segmentDirection c.segment = face.opposite)
    (he : c.segment.start = boundaryPoint w face) (hfirst : c.first = false)
    (goal : Bool) (l : (PrimitiveCode.line c).Labels w) :
    PortPhaseBound w face true (!(if goal then c.target else c.initial))
      ((PrimitiveCode.line c).actor w hw goal l) := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let phase := if goal then c.target else c.initial
  let l' : Line.OwnedLabel w atoms false c.last := ⟨l.val,by simpa only [hfirst] using l.property⟩
  have hpos := Line.owned_position_after_first w (segmentLength c.segment) hw
    (c.above != c.desiredSide) phase c.last l'
  change phase.toNat+2 ≤ Line.position w atoms phase l.val at hpos
  rw [line_actor w hw c hc goal l,hd,he]
  change PortPhaseBound w face true (!phase)
    (Line.along w face.opposite (boundaryPoint w face) (Line.position w atoms phase l.val))
  have hp := Bool.toNat_le phase
  cases hq : phase <;> cases face <;> simp only [hq] at hpos ⊢ <;>
    dsimp [PortPhaseBound,boundarySlot,Line.along,advance,Direction.opposite,boundaryPoint] at * <;>
    simp only [Bool.not_true,Bool.not_false,Bool.toNat_true,Bool.toNat_false,padding,tileStride,spacing] at * <;> omega

theorem gate_actor_phase_bound (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : PrimitiveCode)
    (hc : c ∈ gateCodes w g) (goal : Bool) (l : c.Labels w) (face : Direction)
    (hf : InCollar w face (c.actor w hw goal l)) :
    ∃ role : Fin 3, PortAnnulus.outerDirection (g.pattern,g.rotation,role) = face ∧
      PortPhaseBound w face (g.incoming.get role)
        (portInflow (coreSignals g goal).left (coreSignals g goal).upper (coreSignals g goal).right role)
        (c.actor w hw goal l) := by
  obtain ⟨role,rfl,hd⟩ := gate_actor_collar w hw g c hc goal l face hf
  refine ⟨role,hd,?_⟩
  have hh := line_finish_phase_bound w hw _ (gatePortLine_good w g role) face (g.incoming.get role)
    ((armSpec_last_direction w g role).trans hd)
    (by simpa only [gatePortLine,←hd] using armSpec_last_finish w g role)
    (gatePortLine_last w g role) goal l
  cases goal <;> exact hh

private theorem wire_actor_phase_bound (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args)
    (c : PrimitiveCode)
    (hc : c ∈ wireCodes w q) (goal : Bool) (l : c.Labels w) (face : Direction)
    (hf : InCollar w face (c.actor w hw goal l)) :
    (face = (Catalog.sourceDirection q.1).opposite ∧
      PortPhaseBound w face true (!(if goal then q.2.2 else q.2.1)) (c.actor w hw goal l)) ∨
    (face = Catalog.targetDirection q.1 ∧
      PortPhaseBound w face false (if goal then q.2.2 else q.2.1) (c.actor w hw goal l)) := by
  change c ∈ (wireSpec w q).codes at hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases ((wireSpec w q).mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · obtain ⟨u,hu,ha⟩ := (wireSpec w q).line_actor_at w hw (wireSpec_geometry w q) i hi' goal l
    rcases wire_point_collar_location w q.1 i hi' face 1 (by unfold padding; omega) hu ha hf with h | h
    · rcases h with ⟨rfl,rfl⟩
      refine Or.inl ⟨rfl,?_⟩
      exact line_start_phase_bound w hw _ ((wireSpec w q).line_good w (wireSpec_geometry w q) 0 hi') _
        (by simpa only [Direction.opposite_opposite] using wire_first_direction w q)
        (wire_first_start w q) rfl goal l
    · rcases h with ⟨hlast,rfl⟩
      refine Or.inr ⟨rfl,?_⟩
      exact line_finish_phase_bound w hw _ ((wireSpec w q).line_good w (wireSpec_geometry w q) i hi') _ false
        (wire_last_direction w q i hlast)
        (by simpa only [Bool.toNat_false,advance_zero] using wire_last_finish w q i hlast)
        (by simp only [wireSpec,PathSpec.line,lineCodeAt,ownsLast,hlast,ite_true,Bool.not_false]) goal l
  · exact ((interior_not_collar w face (wire_turn_window_interior w hw q i ht
      (if goal then (PrimitiveCode.matching w hw (.turn ((wireSpec w q).turn i))).target l else
        (PrimitiveCode.matching w hw (.turn ((wireSpec w q).turn i))).source l))) hf).elim

theorem wire_input_phase_bound (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) (c : PrimitiveCode)
    (hc : c ∈ wireCodes w q) (goal : Bool) (l : c.Labels w) (face : Direction)
    (hf : InCollar w face (c.actor w hw goal l)) (hd : face = (Catalog.sourceDirection q.1).opposite) :
    PortPhaseBound w face true (!(if goal then q.2.2 else q.2.1)) (c.actor w hw goal l) := by
  rcases wire_actor_phase_bound w hw q c hc goal l face hf with h | h
  · exact h.2
  · exact (wire_input_ne_output q.1 (hd.symm.trans h.1)).elim

theorem wire_output_phase_bound (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) (c : PrimitiveCode)
    (hc : c ∈ wireCodes w q) (goal : Bool) (l : c.Labels w) (face : Direction)
    (hf : InCollar w face (c.actor w hw goal l)) (hd : face = Catalog.targetDirection q.1) :
    PortPhaseBound w face false (if goal then q.2.2 else q.2.1) (c.actor w hw goal l) := by
  rcases wire_actor_phase_bound w hw q c hc goal l face hf with h | h
  · exact (wire_input_ne_output q.1 (h.1.symm.trans hd)).elim
  · exact h.2

end PushPuzzle.PushS.FiniteRouting
