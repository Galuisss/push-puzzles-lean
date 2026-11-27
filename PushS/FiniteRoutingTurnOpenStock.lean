/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteTurnNormalSlots
public import PushS.FiniteRoutingTurnActionPath
public import PushS.FiniteRoutingTurnCenters
public import PushS.FiniteRoutingSideStock

/-! The actual corner center and its open quadrant contain no normal routed stock. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private def lineActorCell (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (goal : Bool)
    (l : (PrimitiveCode.line c).Labels w) :=
  Line.cell w hw (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))
    (if goal then c.target else c.initial) l.val

private theorem line_actor_action_cell (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (goal : Bool)
    (l : (PrimitiveCode.line c).Labels w) :
    c.actionWorld w hw (lineActorCell w hw c goal l) = (PrimitiveCode.line c).actor w hw goal l := by
  cases goal <;> rfl

private theorem incoming_actor_ne_open_gap (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (t : TurnCode) (hd : segmentDirection c.segment = t.incoming)
    (hf : c.segment.finish = advance t.incoming.opposite t.corner 2)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : Turn.OpenGap w p)
    (goal : Bool) (l : (PrimitiveCode.line c).Labels w) :
    t.actionWorld w hw p ≠ (PrimitiveCode.line c).actor w hw goal l := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let q := if goal then c.target else c.initial
  intro he
  have hxy := c.incoming_turn_coordinates w hw hc t hd hf (lineActorCell w hw c goal l) p
    ((line_actor_action_cell w hw c goal l).trans he.symm)
  change (FiniteTools.radius w+Line.position w atoms q l.val = segmentLength c.segment+2+p.1.val) ∧
    FiniteTools.radius w = (if t.outgoing = rightTurn t.incoming then p.2.val else FiniteTools.side w-(p.2.val+1)) at hxy
  have hb := Line.positions_bounds w hw q atoms (Line.position_mem w atoms q l.val)
  have hq := Bool.toNat_le q
  have hs : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  rw [hs] at hb
  rcases hp with hp | hp
  · by_cases hr : t.outgoing = rightTurn t.incoming <;> simp only [hr,↓reduceIte] at hxy
    all_goals unfold FiniteTools.side FiniteTools.radius at *; omega
  · omega

private theorem outgoing_actor_ne_open_gap (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (t : TurnCode) (ht : Perpendicular t.incoming t.outgoing)
    (hd : segmentDirection c.segment = t.outgoing) (hf : c.segment.start = advance t.outgoing t.corner 1)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : Turn.OpenGap w p)
    (goal : Bool) (l : (PrimitiveCode.line c).Labels w) :
    t.actionWorld w hw p ≠ (PrimitiveCode.line c).actor w hw goal l := by
  intro he
  have hxy := c.outgoing_turn_coordinates w hw hc t ht hd hf (lineActorCell w hw c goal l) p
    ((line_actor_action_cell w hw c goal l).trans he.symm)
  change (FiniteTools.radius w+Line.position w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))
      (if goal then c.target else c.initial) l.val+1 = p.2.val) ∧
    FiniteTools.radius w = (if t.outgoing = rightTurn t.incoming then FiniteTools.side w-(p.1.val+1) else p.1.val) at hxy
  rcases hp with hp | hp
  · by_cases hr : t.outgoing = rightTurn t.incoming <;> simp only [hr,↓reduceIte] at hxy
    all_goals unfold FiniteTools.side FiniteTools.radius at *; omega
  · omega

private theorem TurnCode.own_actor_ne_open_gap (w : ℕ) (hw : 2 ≤ w) (t : TurnCode)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : Turn.OpenGap w p)
    (goal : Bool) (l : Fin 2) : t.actionWorld w hw p ≠ (PrimitiveCode.turn t).actor w hw goal l := by
  let q := if goal then t.target else t.initial
  have hactor : (PrimitiveCode.turn t).actor w hw goal l =
      (PrimitiveCode.turn t).world w hw ((Turn.orientation w t.incoming t.outgoing).cells (Turn.cell w q l)) := by
    cases goal <;> rfl
  rw [hactor]
  intro he
  have hloc := (Turn.orientation w t.incoming t.outgoing).cells.injective ((PrimitiveCode.turn t).world_injective w hw he)
  have hx := congrArg (fun p => p.1.val) hloc
  have hy := congrArg (fun p => p.2.val) hloc
  have hq := Bool.toNat_le q
  rcases hp with hp | hp <;> fin_cases l <;>
    dsimp [Turn.cell,Turn.label,FiniteTools.turnMixedCell,FiniteTools.turnMixedPoint] at hx hy <;>
    unfold FiniteTools.radius at * <;> omega

namespace PathSpec

private theorem open_gap_line_actor_ne (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : P.hasTurn i) (hj : j < P.segments.length)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.turnActive w)
    (hgap : Turn.OpenGap w p) (goal : Bool) (l : (PrimitiveCode.line (P.line j)).Labels w) :
    (P.turn i).actionWorld w hw p ≠ (PrimitiveCode.line (P.line j)).actor w hw goal l := by
  have H := P.junction_contract w G i hi
  by_cases he : j = i
  · subst j
    exact incoming_actor_ne_open_gap w hw _ H.incoming_good _ H.incoming_direction H.incoming_finish p hgap goal l
  by_cases he' : j = i+1
  · subst j
    exact outgoing_actor_ne_open_gap w hw _ H.outgoing_good _ H.perpendicular H.outgoing_direction H.outgoing_start p hgap goal l
  have ha := (P.turn i).action_footprint w hw p hp
  change Nearby 4 ((P.turn i).actionWorld w hw p)
    (padding w+(segmentAt P.segments i).finish.1,padding w+(segmentAt P.segments i).finish.2) at ha
  obtain ⟨v,hv,hv'⟩ := P.line_actor_at w hw G j hj goal l
  by_cases hij : j < i
  · rw [P.join_eq w G i hi.1] at ha
    exact Ne.symm (P.marks_ne w G j (i+1) hj hi.1 (by omega) 1 4 (by unfold FiniteGeometry.origin; omega)
      hv (P.start_contains w G (i+1) hi.1) hv' ha)
  · exact P.marks_ne w G i j (by have hh := hi.1; omega) hj (by omega) 4 1
      (by unfold FiniteGeometry.origin; omega) (P.finish_contains w G i (by have hh := hi.1; omega)) hv ha hv'

private theorem open_gap_turn_actor_ne (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : P.hasTurn i) (hj : P.hasTurn j)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.turnActive w)
    (hgap : Turn.OpenGap w p) (goal : Bool) (l : Fin 2) :
    (P.turn i).actionWorld w hw p ≠ (PrimitiveCode.turn (P.turn j)).actor w hw goal l := by
  have ha := (P.turn i).action_footprint w hw p hp
  change Nearby 4 ((P.turn i).actionWorld w hw p)
    (padding w+(segmentAt P.segments i).finish.1,padding w+(segmentAt P.segments i).finish.2) at ha
  have hb := P.turn_actor_at w hw G j hj goal l
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [P.join_eq w G j hj.1] at hb
    exact P.marks_ne w G i (j+1) (by have hh := hi.1; omega) hj.1 (by omega) 4 2
      (by unfold FiniteGeometry.origin; omega) (P.finish_contains w G i (by have hh := hi.1; omega))
      (P.start_contains w G (j+1) hj.1) ha hb
  · subst j
    exact (P.turn i).own_actor_ne_open_gap w hw p hgap goal l
  · rw [P.join_eq w G i hi.1] at ha
    exact Ne.symm (P.marks_ne w G j (i+1) (by have hh := hj.1; omega) hi.1 (by omega) 2 4
      (by unfold FiniteGeometry.origin; omega) (P.finish_contains w G j (by have hh := hj.1; omega))
      (P.start_contains w G (i+1) hi.1) hb ha)

private theorem open_gap_codes_actor_ne (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : P.hasTurn i) (p : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hp : p ∈ FiniteTools.turnActive w) (hgap : Turn.OpenGap w p)
    (c : PrimitiveCode) (hc : c ∈ P.codes) (goal : Bool) (l : c.Labels w) :
    (P.turn i).actionWorld w hw p ≠ c.actor w hw goal l := by
  obtain ⟨j,hj,hc⟩ := List.mem_flatMap.mp hc
  rcases (P.mem_block j c).mp hc with rfl | ⟨ht,rfl⟩
  · exact P.open_gap_line_actor_ne w hw G i j hi (List.mem_range.mp hj) p hp hgap goal l
  · exact P.open_gap_turn_actor_ne w hw G i j hi ht p hp hgap goal l

end PathSpec

private theorem gate_open_gap_actor_ne (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : TurnCode)
    (hc : .turn c ∈ gateCodes w g) (p : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hp : p ∈ FiniteTools.turnActive w) (hgap : Turn.OpenGap w p)
    (d : PrimitiveCode) (hd : d ∈ gateCodes w g) (goal : Bool) (l : d.Labels w) :
    c.actionWorld w hw p ≠ d.actor w hw goal l := by
  obtain ⟨role,i,hi,rfl⟩ := gate_turn_origin w g c hc
  let P := armSpec w g role
  have G : P.Geometry w := armSpec_geometry w g role
  have ha := P.turn_action_at w hw G i hi p hp
  have hu := P.start_contains w G (i+1) hi.1
  rw [gateCodes_eq_specs] at hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact core_tail_actor_ne w hw g role 4 (by unfold FiniteGeometry.origin; omega)
      ⟨_,P.segment_mem_tail (i+1) hi.1 (by omega),hu⟩ ha goal l
  · obtain ⟨other,_,hd⟩ := List.mem_flatMap.mp hd
    by_cases he : role = other
    · subst other
      exact P.open_gap_codes_actor_ne w hw G i hi p hp hgap d hd goal l
    · obtain ⟨v,hv,hv'⟩ := (armSpec w g other).code_actor_trace w hw (armSpec_geometry w g other) d hd goal l
      apply footprint_ne (w := w) (m := 4) (n := 2) _ ha hv'
      intro hnear
      exact armRoutes_separated_wide w g he ⟨_,P.segment_mem (i+1) hi.1,hu⟩ hv (nearby_of_le (by omega) hnear)

theorem local_open_gap_actor_ne (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : TurnCode)
    (hc : .turn c ∈ FiniteSourceInventory.localCodes w code) (p : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hp : p ∈ FiniteTools.turnActive w) (hgap : Turn.OpenGap w p)
    (d : PrimitiveCode) (hd : d ∈ FiniteSourceInventory.localCodes w code) (goal : Bool) (l : d.Labels w) :
    c.actionWorld w hw p ≠ d.actor w hw goal l := by
  exact localCodes_pair_elim hc hd
    (fun g hcg hdg => gate_open_gap_actor_ne w hw g.2 c hcg p hp hgap d hdg goal l)
    (fun q hcq hdq => by
      obtain ⟨i,hi,rfl⟩ := (wireSpec w q.2).turn_code_origin c hcq
      exact (wireSpec w q.2).open_gap_codes_actor_ne w hw (wireSpec_geometry w q.2) i hi p hp hgap d hdq goal l)

end PushPuzzle.PushS.FiniteRouting
