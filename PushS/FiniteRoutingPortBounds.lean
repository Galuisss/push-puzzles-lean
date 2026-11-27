/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingMacroGeometry

/-! Consuming ports leave a two-cell ownership gap beyond every producing endpoint. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

def PortOwnedBound (w : ℕ) (face : Direction) (incoming : Bool) (a : ℕ × ℕ) : Prop :=
  match face with
  | .east => if incoming then a.1+2 ≤ padding w+tileStride w else a.1 ≤ padding w+tileStride w+1
  | .south => if incoming then a.2+2 ≤ padding w+tileStride w else a.2 ≤ padding w+tileStride w+1
  | .west => if incoming then padding w+2 ≤ a.1 else padding w ≤ a.1+1
  | .north => if incoming then padding w+2 ≤ a.2 else padding w ≤ a.2+1

theorem line_finish_owned_bound (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (face : Direction) (incoming : Bool) (hd : segmentDirection c.segment = face)
    (he : c.segment.finish = advance face.opposite (boundaryPoint w face) incoming.toNat)
    (hlast : c.last = !incoming) (goal : Bool) (l : (PrimitiveCode.line c).Labels w) :
    PortOwnedBound w face incoming ((PrimitiveCode.line c).actor w hw goal l) := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let phase := if goal then c.target else c.initial
  have hlen := Line.program_span_of_bound w (segmentLength c.segment) (c.above != c.desiredSide) hc.2.1
  have hp := Line.positions_bounds w hw phase atoms (Line.position_mem w atoms phase l.val)
  change Line.span w atoms = segmentLength c.segment at hlen
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
  change PortOwnedBound w face incoming (Line.along w face c.segment.start (Line.position w atoms phase l.val))
  cases incoming <;> cases face <;>
    dsimp [PortOwnedBound,Travels,advance,Line.along,Direction.opposite,boundaryPoint] at * <;>
    simp only [padding,tileStride,spacing] at * <;> omega

theorem line_start_owned_bound (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (face : Direction) (hd : segmentDirection c.segment = face.opposite)
    (he : c.segment.start = boundaryPoint w face) (hfirst : c.first = false)
    (goal : Bool) (l : (PrimitiveCode.line c).Labels w) :
    PortOwnedBound w face true ((PrimitiveCode.line c).actor w hw goal l) := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let phase := if goal then c.target else c.initial
  let l' : Line.OwnedLabel w atoms false c.last := ⟨l.val,by simpa only [hfirst] using l.property⟩
  have hpos := Line.owned_position_after_first w (segmentLength c.segment) hw (c.above != c.desiredSide) phase c.last l'
  change phase.toNat+2 ≤ Line.position w atoms phase l.val at hpos
  rw [line_actor w hw c hc goal l,hd,he]
  change PortOwnedBound w face true (Line.along w face.opposite (boundaryPoint w face) (Line.position w atoms phase l.val))
  cases face <;> dsimp [PortOwnedBound,Line.along,Direction.opposite,boundaryPoint] at * <;>
    simp only [padding,tileStride,spacing] at * <;> omega

theorem gatePortLine_last (w : ℕ) (g : GateTileState) (role : Fin 3) :
    (gatePortLine w g role).last = !(g.incoming.get role) := by
  have hi : (armRoute w g role).length-1+1 = (armRoute w g role).length := by rw [armRoute_length,route_length]; omega
  simp only [gatePortLine,PathSpec.line,lineCodeAt,ownsLast,armSpec,hi,ite_true]

theorem gate_actor_collar_bound (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : PrimitiveCode)
    (hc : c ∈ gateCodes w g) (goal : Bool) (l : c.Labels w) (face : Direction)
    (hf : InCollar w face (c.actor w hw goal l)) :
    ∃ role : Fin 3, PortAnnulus.outerDirection (g.pattern,g.rotation,role) = face ∧
      PortOwnedBound w face (g.incoming.get role) (c.actor w hw goal l) := by
  obtain ⟨role,rfl,hd⟩ := gate_actor_collar w hw g c hc goal l face hf
  refine ⟨role,hd,?_⟩
  apply line_finish_owned_bound w hw _ (gatePortLine_good w g role) face (g.incoming.get role) _ _
    (gatePortLine_last w g role) goal l
  · exact (armSpec_last_direction w g role).trans hd
  · simpa only [gatePortLine,←hd] using armSpec_last_finish w g role

theorem wire_point_collar_location (w : ℕ) (kind : Catalog.Kind) (i : ℕ)
    (hi : i < (wireRoute w kind).length) (face : Direction) (m : ℕ) (hm : m ≤ padding w)
    {u a : ℕ × ℕ} (hu : (segmentAt (wireRoute w kind) i).Contains u)
    (ha : Nearby m a (padding w+u.1,padding w+u.2)) (hf : InCollar w face a) :
    (i = 0 ∧ face = (Catalog.sourceDirection kind).opposite) ∨
      (i+1 = (wireRoute w kind).length ∧ face = Catalog.targetDirection kind) := by
  have hlen : (wireRoute w kind).length ≤ 2 := by rw [wireRoute_length]; split_ifs <;> omega
  have hidx : i = 0 ∨ i = 1 := by omega
  have hb := Segment.coordinate_bounds hu
  clear hu
  rcases hidx with rfl | rfl <;> cases kind <;> cases face <;>
    simp [wireRoute,wireVertices,Catalog.sourceDirection,Catalog.targetDirection,Direction.opposite] at hi ⊢ <;>
    simp [wireRoute,wireVertices,segmentAt] at hb <;>
    dsimp [InCollar,Nearby] at * <;> simp only [tileStride,spacing,padding] at * <;> omega

theorem wire_first_start (w : ℕ) (q : Catalog.Bitmap.Args) :
    ((wireSpec w q).line 0).segment.start = boundaryPoint w (Catalog.sourceDirection q.1).opposite := by
  change (trimmedSegment (wireRoute w q.1) 0).start = _
  simp only [trimmedSegment,trimmed,startTrim,ite_true,advance_zero]
  rcases q with ⟨kind,initial,target⟩
  cases kind <;> simp [wireRoute,wireVertices,segmentAt,Catalog.sourceDirection,Direction.opposite,boundaryPoint]

theorem wire_first_direction (w : ℕ) (q : Catalog.Bitmap.Args) :
    segmentDirection ((wireSpec w q).line 0).segment = Catalog.sourceDirection q.1 := by
  change segmentDirection (trimmedSegment (wireRoute w q.1) 0) = _
  rw [trimmedSegment_direction w _ (wireRoute_good w q.1) 0
    (by rw [wireRoute_length]; split_ifs <;> decide)]
  rcases q with ⟨kind,initial,target⟩
  cases kind <;> simp [wireRoute,wireVertices,segmentAt,segmentDirection,Catalog.sourceDirection,tileStride,spacing]

theorem wire_last_finish (w : ℕ) (q : Catalog.Bitmap.Args) (i : ℕ) (hi : i+1 = (wireRoute w q.1).length) :
    ((wireSpec w q).line i).segment.finish = boundaryPoint w (Catalog.targetDirection q.1) := by
  change (trimmedSegment (wireRoute w q.1) i).finish = _
  simp only [trimmedSegment,trimmed,finishTrim,hi,ite_true,advance_zero]
  have hiz : i = (wireRoute w q.1).length-1 := by omega
  rw [hiz]
  rcases q with ⟨kind,initial,target⟩
  cases kind <;> simp [wireRoute,wireVertices,segmentAt,Catalog.targetDirection,boundaryPoint]

theorem wire_last_direction (w : ℕ) (q : Catalog.Bitmap.Args) (i : ℕ) (hi : i+1 = (wireRoute w q.1).length) :
    segmentDirection ((wireSpec w q).line i).segment = Catalog.targetDirection q.1 := by
  change segmentDirection (trimmedSegment (wireRoute w q.1) i) = _
  rw [trimmedSegment_direction w _ (wireRoute_good w q.1) i (by omega)]
  have hiz : i = (wireRoute w q.1).length-1 := by omega
  rw [hiz]
  rcases q with ⟨kind,initial,target⟩
  cases kind <;> simp [wireRoute,wireVertices,segmentAt,segmentDirection,Catalog.targetDirection,tileStride,spacing]

theorem wire_actor_collar_bound (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) (c : PrimitiveCode)
    (hc : c ∈ wireCodes w q) (goal : Bool) (l : c.Labels w) (face : Direction)
    (hf : InCollar w face (c.actor w hw goal l)) :
    (face = (Catalog.sourceDirection q.1).opposite ∧ PortOwnedBound w face true (c.actor w hw goal l)) ∨
      (face = Catalog.targetDirection q.1 ∧ PortOwnedBound w face false (c.actor w hw goal l)) := by
  change c ∈ (wireSpec w q).codes at hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases ((wireSpec w q).mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · obtain ⟨u,hu,ha⟩ := (wireSpec w q).line_actor_at w hw (wireSpec_geometry w q) i hi' goal l
    rcases wire_point_collar_location w q.1 i hi' face 1 (by unfold padding; omega) hu ha hf with h | h
    · rcases h with ⟨rfl,rfl⟩
      refine Or.inl ⟨rfl,?_⟩
      apply line_start_owned_bound w hw _ ((wireSpec w q).line_good w (wireSpec_geometry w q) 0 hi')
        _ _ (wire_first_start w q) rfl goal l
      simpa only [Direction.opposite_opposite] using wire_first_direction w q
    · rcases h with ⟨hlast,rfl⟩
      refine Or.inr ⟨rfl,?_⟩
      apply line_finish_owned_bound w hw _ ((wireSpec w q).line_good w (wireSpec_geometry w q) i hi')
        _ false (wire_last_direction w q i hlast) _ _ goal l
      · simpa only [Bool.toNat_false,advance_zero] using wire_last_finish w q i hlast
      · simp only [wireSpec,PathSpec.line,lineCodeAt,ownsLast,hlast,ite_true,Bool.not_false]
  · exact ((interior_not_collar w face (wire_turn_window_interior w hw q i ht
      (if goal then (PrimitiveCode.matching w hw (.turn ((wireSpec w q).turn i))).target l else
        (PrimitiveCode.matching w hw (.turn ((wireSpec w q).turn i))).source l))) hf).elim

theorem wire_input_ne_output (kind : Catalog.Kind) :
    (Catalog.sourceDirection kind).opposite ≠ Catalog.targetDirection kind := by cases kind <;> decide

theorem wire_input_actor_bound (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) (c : PrimitiveCode)
    (hc : c ∈ wireCodes w q) (goal : Bool) (l : c.Labels w) (face : Direction)
    (hf : InCollar w face (c.actor w hw goal l)) (hd : face = (Catalog.sourceDirection q.1).opposite) :
    PortOwnedBound w face true (c.actor w hw goal l) := by
  rcases wire_actor_collar_bound w hw q c hc goal l face hf with h | h
  · exact h.2
  · exact (wire_input_ne_output q.1 (hd.symm.trans h.1)).elim

theorem wire_output_actor_bound (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) (c : PrimitiveCode)
    (hc : c ∈ wireCodes w q) (goal : Bool) (l : c.Labels w) (face : Direction)
    (hf : InCollar w face (c.actor w hw goal l)) (hd : face = Catalog.targetDirection q.1) :
    PortOwnedBound w face false (c.actor w hw goal l) := by
  rcases wire_actor_collar_bound w hw q c hc goal l face hf with h | h
  · exact (wire_input_ne_output q.1 (h.1.symm.trans hd)).elim
  · exact h.2

def LocalPort : CellPlan.Code → Direction → Bool → Prop
  | none,_,_ => False
  | some (.inl (_,g)),face,incoming =>
      ∃ role : Fin 3, PortAnnulus.outerDirection (g.pattern,g.rotation,role) = face ∧ g.incoming.get role = incoming
  | some (.inr (_,q)),face,incoming =>
      (incoming = true ∧ face = (Catalog.sourceDirection q.1).opposite) ∨
        (incoming = false ∧ face = Catalog.targetDirection q.1)

end PushPuzzle.PushS.FiniteRouting
