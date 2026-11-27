/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingStaticRows
public import PushS.FiniteRoutingPathClearance
public import PushS.FiniteRoutingPathInventory

/-! Actual complete line rows avoid every wall of their emitted multi-segment path. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side

namespace LineCode

private theorem row_ne_collinear_wall (w : ℕ) (hw : 2 ≤ w) (c d : LineCode)
    (hc : LineGood w c.segment) (hd : LineGood w d.segment)
    (hdir : segmentDirection c.segment = segmentDirection d.segment) (hjoin : c.segment.finish = d.segment.start)
    (n : ℕ) (hn : n ≤ segmentLength c.segment+1)
    (p : Cell ((PrimitiveCode.line d).instanceOf w hw).width ((PrimitiveCode.line d).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line d).instanceOf w hw).board.walls) :
    c.rowWorld w hw hc n hn ≠ (PrimitiveCode.line d).world w hw p := by
  obtain ⟨_,_,hrow⟩ := line_wall_envelope w hw d hd p hp
  have ht := segment_travels c.segment hc.1
  intro he
  rw [←he,rowWorld_eq,←hdir,←hjoin] at hrow
  cases hdi : segmentDirection c.segment <;> simp only [hdi] at ht hrow <;>
    dsimp [Travels,SameLane,Line.along] at ht hrow <;> omega

private theorem next_row_ne_collinear_wall (w : ℕ) (hw : 2 ≤ w) (c d : LineCode)
    (hc : LineGood w c.segment) (hd : LineGood w d.segment)
    (hdir : segmentDirection c.segment = segmentDirection d.segment) (hjoin : c.segment.finish = d.segment.start)
    (n : ℕ) (hn : n ≤ segmentLength d.segment+1)
    (p : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) :
    d.rowWorld w hw hd n hn ≠ (PrimitiveCode.line c).world w hw p := by
  obtain ⟨_,_,hrow⟩ := line_wall_envelope w hw c hc p hp
  have ht := segment_travels c.segment hc.1
  intro he
  rw [←he,rowWorld_eq,←hdir,←hjoin] at hrow
  cases hdi : segmentDirection c.segment <;> simp only [hdi] at ht hrow <;>
    dsimp [Travels,SameLane,Line.along] at ht hrow <;> omega

end LineCode

namespace PathSpec

theorem line_row_at (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w) (i : ℕ)
    (hi : i < P.segments.length) (n : ℕ) (hn : n ≤ segmentLength (P.line i).segment+1) :
    ∃ u, (segmentAt P.segments i).Contains u ∧
      Nearby 1 ((P.line i).rowWorld w hw (P.line_good w G i hi) n hn) (padding w+u.1,padding w+u.2) := by
  obtain ⟨u,hu,ha⟩ := (P.line i).row_footprint w hw (P.line_good w G i hi) n hn
  have hs := G.good _ (P.segment_mem i hi)
  exact ⟨u,trimmed_trace_subset _ hs.1 _ _
    (by have hf := startTrim_bound P.segments i; have hb := finishTrim_bound P.segments i
        have hl := hs.2.1; omega) hu,ha⟩

private theorem row_line_wall_forward (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : j < P.segments.length) (hij : i < j)
    (n : ℕ) (hn : n ≤ segmentLength (P.line i).segment+1)
    (p : Cell ((PrimitiveCode.line (P.line j)).instanceOf w hw).width ((PrimitiveCode.line (P.line j)).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line (P.line j)).instanceOf w hw).board.walls) :
    (P.line i).rowWorld w hw (P.line_good w G i hi) n hn ≠ (PrimitiveCode.line (P.line j)).world w hw p := by
  by_cases he : j = i+1
  · subst j
    by_cases ht : P.hasTurn i
    · have H := P.junction_contract w G i ht
      rw [LineCode.incoming_row_ray w hw _ _ H.incoming_good H.incoming_direction H.incoming_finish]
      exact incoming_ray_ne_outgoing_wall w hw _ _ H.outgoing_good H.perpendicular H.outgoing_direction H.outgoing_start _ p hp
    · have H := P.collinear_contract w G i hj ht
      exact LineCode.row_ne_collinear_wall w hw _ _ H.first_good H.next_good H.directions H.joined n hn p hp
  · obtain ⟨u,hu,ha⟩ := P.line_row_at w hw G i hi n hn
    obtain ⟨v,hv,hb⟩ := P.line_wall_at w hw G j hj p hp
    exact P.marks_ne w G i j hi hj (by omega) 1 (w+1) (by unfold FiniteGeometry.origin; omega) hu hv ha hb

private theorem row_line_wall_backward (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : j < P.segments.length) (hij : i < j)
    (n : ℕ) (hn : n ≤ segmentLength (P.line j).segment+1)
    (p : Cell ((PrimitiveCode.line (P.line i)).instanceOf w hw).width ((PrimitiveCode.line (P.line i)).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line (P.line i)).instanceOf w hw).board.walls) :
    (P.line j).rowWorld w hw (P.line_good w G j hj) n hn ≠ (PrimitiveCode.line (P.line i)).world w hw p := by
  by_cases he : j = i+1
  · subst j
    by_cases ht : P.hasTurn i
    · have H := P.junction_contract w G i ht
      rw [LineCode.outgoing_row_ray w hw _ _ H.outgoing_good H.outgoing_direction H.outgoing_start]
      exact outgoing_ray_ne_incoming_wall w hw _ _ H.incoming_good H.perpendicular H.incoming_direction H.incoming_finish _ p hp
    · have H := P.collinear_contract w G i hj ht
      exact LineCode.next_row_ne_collinear_wall w hw _ _ H.first_good H.next_good H.directions H.joined n hn p hp
  · obtain ⟨u,hu,ha⟩ := P.line_wall_at w hw G i hi p hp
    obtain ⟨v,hv,hb⟩ := P.line_row_at w hw G j hj n hn
    exact Ne.symm (P.marks_ne w G i j hi hj (by omega) (w+1) 1
      (by unfold FiniteGeometry.origin; omega) hu hv ha hb)

private theorem row_line_wall_ne (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : j < P.segments.length)
    (n : ℕ) (hn : n ≤ segmentLength (P.line i).segment+1)
    (p : Cell ((PrimitiveCode.line (P.line j)).instanceOf w hw).width ((PrimitiveCode.line (P.line j)).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line (P.line j)).instanceOf w hw).board.walls) :
    (P.line i).rowWorld w hw (P.line_good w G i hi) n hn ≠ (PrimitiveCode.line (P.line j)).world w hw p := by
  rcases lt_trichotomy i j with h | h | h
  · exact P.row_line_wall_forward w hw G i j hi hj h n hn p hp
  · subst j
    exact (P.line i).row_ne_own_wall w hw (P.line_good w G i hi) n hn p hp
  · exact P.row_line_wall_backward w hw G j i hj hi h n hn p hp

private theorem row_turn_wall_ne (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : P.hasTurn j)
    (n : ℕ) (hn : n ≤ segmentLength (P.line i).segment+1)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hp : p ∈ ((PrimitiveCode.turn (P.turn j)).instanceOf w hw).board.walls) :
    (P.line i).rowWorld w hw (P.line_good w G i hi) n hn ≠ (PrimitiveCode.turn (P.turn j)).world w hw p := by
  have H := P.junction_contract w G j hj
  by_cases he : i = j
  · subst i
    rw [LineCode.incoming_row_ray w hw _ _ H.incoming_good H.incoming_direction H.incoming_finish]
    exact Ne.symm (turn_wall_ne_ray w hw _ H.perpendicular true _ p hp)
  by_cases he' : i = j+1
  · subst i
    rw [LineCode.outgoing_row_ray w hw _ _ H.outgoing_good H.outgoing_direction H.outgoing_start]
    exact Ne.symm (turn_wall_ne_ray w hw _ H.perpendicular false _ p hp)
  by_cases hij : i < j
  · obtain ⟨u,hu,ha⟩ := P.line_row_at w hw G i hi n hn
    have hb := P.turn_wall_at w hw j p
    rw [P.join_eq w G j hj.1] at hb
    exact P.marks_ne w G i (j+1) hi hj.1 (by omega) 1 (FiniteTools.radius w)
      (by unfold FiniteGeometry.origin FiniteTools.radius; omega) hu (P.start_contains w G (j+1) hj.1) ha hb
  · obtain ⟨v,hv,hb⟩ := P.line_row_at w hw G i hi n hn
    have ha := P.turn_wall_at w hw j p
    exact Ne.symm (P.marks_ne w G j i (by omega) hi (by omega) (FiniteTools.radius w) 1
      (by unfold FiniteGeometry.origin FiniteTools.radius; omega) (P.finish_contains w G j (by omega)) hv ha hb)

theorem row_codes_wall_clear (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : i < P.segments.length) (n : ℕ) (hn : n ≤ segmentLength (P.line i).segment+1)
    (c : PrimitiveCode) (hc : c ∈ P.codes)
    (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height) (hp : p ∈ (c.instanceOf w hw).board.walls) :
    (P.line i).rowWorld w hw (P.line_good w G i hi) n hn ≠ c.world w hw p := by
  obtain ⟨j,hj,hc⟩ := List.mem_flatMap.mp hc
  have hj' := List.mem_range.mp hj
  rcases (P.mem_block j c).mp hc with rfl | ⟨ht,rfl⟩
  · exact P.row_line_wall_ne w hw G i j hi hj' n hn p hp
  · exact P.row_turn_wall_ne w hw G i j hi ht n hn p hp

end PathSpec

end PushPuzzle.PushS.FiniteRouting
