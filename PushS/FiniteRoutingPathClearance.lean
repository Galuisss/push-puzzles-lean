/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPathLayout
public import PushS.FiniteRoutingInventoryGeometry

/-! Complete physical actor separation and wall clearance along the indexed emitted path. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.PathSpec

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteTools.turnWalls

theorem lines_actor_ne (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : j < P.segments.length) (hij : i < j)
    (goal : Bool) (l : (PrimitiveCode.line (P.line i)).Labels w) (r : (PrimitiveCode.line (P.line j)).Labels w) :
    (PrimitiveCode.line (P.line i)).actor w hw goal l ≠ (PrimitiveCode.line (P.line j)).actor w hw goal r := by
  by_cases he : j = i+1
  · subst j
    by_cases ht : P.hasTurn i
    · have hc := P.junction_contract w G i ht
      exact incoming_line_actor_ne_outgoing_actor w hw _ _ _ hc.incoming_good hc.outgoing_good
        hc.perpendicular hc.incoming_last hc.outgoing_first hc.incoming_direction hc.incoming_finish
        hc.outgoing_direction hc.outgoing_start goal goal l r
    · have hc := P.collinear_contract w G i hj ht
      exact collinear_actor_ne_actor w hw _ _ hc.first_good hc.next_good hc.next_first hc.directions hc.joined goal goal l r
  · obtain ⟨u,hu,ha⟩ := P.line_actor_at w hw G i hi goal l
    obtain ⟨v,hv,hb⟩ := P.line_actor_at w hw G j hj goal r
    exact P.marks_ne w G i j hi hj (by omega) 1 1 (by unfold FiniteGeometry.origin; omega) hu hv ha hb

private theorem lines_actor_wall_forward (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : j < P.segments.length) (hij : i < j)
    (goal : Bool) (l : (PrimitiveCode.line (P.line i)).Labels w)
    (p : Cell ((PrimitiveCode.line (P.line j)).instanceOf w hw).width ((PrimitiveCode.line (P.line j)).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line (P.line j)).instanceOf w hw).board.walls) :
    (PrimitiveCode.line (P.line i)).actor w hw goal l ≠ (PrimitiveCode.line (P.line j)).world w hw p := by
  by_cases he : j = i+1
  · subst j
    by_cases ht : P.hasTurn i
    · have hc := P.junction_contract w G i ht
      exact incoming_line_actor_ne_outgoing_wall w hw _ _ _ hc.incoming_good hc.outgoing_good
        hc.perpendicular hc.incoming_last hc.incoming_direction hc.incoming_finish
        hc.outgoing_direction hc.outgoing_start goal l p hp
    · have hc := P.collinear_contract w G i hj ht
      exact collinear_actor_ne_wall w hw _ _ hc.first_good hc.next_good hc.directions hc.joined goal l p hp
  · obtain ⟨u,hu,ha⟩ := P.line_actor_at w hw G i hi goal l
    obtain ⟨v,hv,hb⟩ := P.line_wall_at w hw G j hj p hp
    exact P.marks_ne w G i j hi hj (by omega) 1 (w+1) (by unfold FiniteGeometry.origin; omega) hu hv ha hb

private theorem lines_actor_wall_backward (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : j < P.segments.length) (hij : i < j)
    (goal : Bool) (l : (PrimitiveCode.line (P.line j)).Labels w)
    (p : Cell ((PrimitiveCode.line (P.line i)).instanceOf w hw).width ((PrimitiveCode.line (P.line i)).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line (P.line i)).instanceOf w hw).board.walls) :
    (PrimitiveCode.line (P.line j)).actor w hw goal l ≠ (PrimitiveCode.line (P.line i)).world w hw p := by
  by_cases he : j = i+1
  · subst j
    by_cases ht : P.hasTurn i
    · have hc := P.junction_contract w G i ht
      exact outgoing_line_actor_ne_incoming_wall w hw _ _ _ hc.incoming_good hc.outgoing_good
        hc.perpendicular hc.outgoing_first hc.incoming_direction hc.incoming_finish
        hc.outgoing_direction hc.outgoing_start goal l p hp
    · have hc := P.collinear_contract w G i hj ht
      exact collinear_next_actor_ne_wall w hw _ _ hc.first_good hc.next_good hc.directions hc.joined goal l p hp
  · obtain ⟨u,hu,ha⟩ := P.line_wall_at w hw G i hi p hp
    obtain ⟨v,hv,hb⟩ := P.line_actor_at w hw G j hj goal l
    exact Ne.symm (P.marks_ne w G i j hi hj (by omega) (w+1) 1
      (by unfold FiniteGeometry.origin; omega) hu hv ha hb)

theorem lines_actor_wall_ne (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : j < P.segments.length)
    (goal : Bool) (l : (PrimitiveCode.line (P.line i)).Labels w)
    (p : Cell ((PrimitiveCode.line (P.line j)).instanceOf w hw).width ((PrimitiveCode.line (P.line j)).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line (P.line j)).instanceOf w hw).board.walls) :
    (PrimitiveCode.line (P.line i)).actor w hw goal l ≠ (PrimitiveCode.line (P.line j)).world w hw p := by
  rcases lt_trichotomy i j with h | h | h
  · exact P.lines_actor_wall_forward w hw G i j hi hj h goal l p hp
  · subst j
    exact PrimitiveCode.actor_ne_own_wall w hw _ goal l p hp
  · exact P.lines_actor_wall_backward w hw G j i hj hi h goal l p hp

theorem line_turn_actor_ne (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : P.hasTurn j)
    (goal : Bool) (l : (PrimitiveCode.line (P.line i)).Labels w) (r : Fin 2) :
    (PrimitiveCode.line (P.line i)).actor w hw goal l ≠ (PrimitiveCode.turn (P.turn j)).actor w hw goal r := by
  have hc := P.junction_contract w G j hj
  by_cases he : i = j
  · subst i
    exact incoming_line_actor_ne_turn_actor w hw _ _ hc.incoming_good hc.perpendicular hc.incoming_last
      hc.incoming_direction hc.incoming_finish goal goal l r
  by_cases he' : i = j+1
  · subst i
    exact outgoing_line_actor_ne_turn_actor w hw _ _ hc.outgoing_good hc.perpendicular hc.outgoing_first
      hc.outgoing_direction hc.outgoing_start goal goal l r
  by_cases hij : i < j
  · obtain ⟨u,hu,ha⟩ := P.line_actor_at w hw G i hi goal l
    have hb := P.turn_actor_at w hw G j hj goal r
    rw [P.join_eq w G j hj.1] at hb
    exact P.marks_ne w G i (j+1) hi hj.1 (by omega) 1 2 (by unfold FiniteGeometry.origin; omega)
      hu (P.start_contains w G (j+1) hj.1) ha hb
  · obtain ⟨v,hv,hb⟩ := P.line_actor_at w hw G i hi goal l
    have ha := P.turn_actor_at w hw G j hj goal r
    exact Ne.symm (P.marks_ne w G j i (by omega) hi (by omega) 2 1
      (by unfold FiniteGeometry.origin; omega) (P.finish_contains w G j (by omega)) hv ha hb)

theorem line_turn_wall_ne (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : P.hasTurn j)
    (goal : Bool) (l : (PrimitiveCode.line (P.line i)).Labels w)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hp : p ∈ ((PrimitiveCode.turn (P.turn j)).instanceOf w hw).board.walls) :
    (PrimitiveCode.line (P.line i)).actor w hw goal l ≠ (PrimitiveCode.turn (P.turn j)).world w hw p := by
  have hc := P.junction_contract w G j hj
  by_cases he : i = j
  · subst i
    exact incoming_line_actor_ne_turn_wall w hw _ _ hc.incoming_good hc.perpendicular hc.incoming_last
      hc.incoming_direction hc.incoming_finish goal l p hp
  by_cases he' : i = j+1
  · subst i
    exact outgoing_line_actor_ne_turn_wall w hw _ _ hc.outgoing_good hc.perpendicular hc.outgoing_first
      hc.outgoing_direction hc.outgoing_start goal l p hp
  by_cases hij : i < j
  · obtain ⟨u,hu,ha⟩ := P.line_actor_at w hw G i hi goal l
    have hb := P.turn_wall_at w hw j p
    rw [P.join_eq w G j hj.1] at hb
    exact P.marks_ne w G i (j+1) hi hj.1 (by omega) 1 (FiniteTools.radius w)
      (by unfold FiniteGeometry.origin FiniteTools.radius; omega) hu (P.start_contains w G (j+1) hj.1) ha hb
  · obtain ⟨v,hv,hb⟩ := P.line_actor_at w hw G i hi goal l
    have ha := P.turn_wall_at w hw j p
    exact Ne.symm (P.marks_ne w G j i (by omega) hi (by omega) (FiniteTools.radius w) 1
      (by unfold FiniteGeometry.origin FiniteTools.radius; omega) (P.finish_contains w G j (by omega)) hv ha hb)

theorem turn_line_wall_ne (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : P.hasTurn j)
    (goal : Bool) (r : Fin 2)
    (p : Cell ((PrimitiveCode.line (P.line i)).instanceOf w hw).width ((PrimitiveCode.line (P.line i)).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line (P.line i)).instanceOf w hw).board.walls) :
    (PrimitiveCode.turn (P.turn j)).actor w hw goal r ≠ (PrimitiveCode.line (P.line i)).world w hw p := by
  have hc := P.junction_contract w G j hj
  by_cases he : i = j
  · subst i
    exact turn_actor_ne_incoming_wall w hw _ _ hc.incoming_good hc.perpendicular
      hc.incoming_direction hc.incoming_finish goal r p hp
  by_cases he' : i = j+1
  · subst i
    exact turn_actor_ne_outgoing_wall w hw _ _ hc.outgoing_good hc.perpendicular
      hc.outgoing_direction hc.outgoing_start goal r p hp
  by_cases hij : i < j
  · obtain ⟨u,hu,ha⟩ := P.line_wall_at w hw G i hi p hp
    have hb := P.turn_actor_at w hw G j hj goal r
    rw [P.join_eq w G j hj.1] at hb
    exact Ne.symm (P.marks_ne w G i (j+1) hi hj.1 (by omega) (w+1) 2
      (by unfold FiniteGeometry.origin; omega) hu (P.start_contains w G (j+1) hj.1) ha hb)
  · obtain ⟨v,hv,hb⟩ := P.line_wall_at w hw G i hi p hp
    have ha := P.turn_actor_at w hw G j hj goal r
    exact P.marks_ne w G j i (by omega) hi (by omega) 2 (w+1)
      (by unfold FiniteGeometry.origin; omega) (P.finish_contains w G j (by omega)) hv ha hb

theorem turns_actor_ne (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : P.hasTurn i) (hj : P.hasTurn j) (hij : i < j)
    (goal : Bool) (l r : Fin 2) :
    (PrimitiveCode.turn (P.turn i)).actor w hw goal l ≠ (PrimitiveCode.turn (P.turn j)).actor w hw goal r := by
  have hil := hi.1
  have hjl := hj.1
  have ha := P.turn_actor_at w hw G i hi goal l
  have hb := P.turn_actor_at w hw G j hj goal r
  rw [P.join_eq w G j hj.1] at hb
  exact P.marks_ne w G i (j+1) (by omega) hj.1 (by omega) 2 2
    (by unfold FiniteGeometry.origin; omega) (P.finish_contains w G i (by omega))
    (P.start_contains w G (j+1) hj.1) ha hb

theorem turns_actor_wall_ne (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : P.hasTurn i) (hj : P.hasTurn j) (goal : Bool) (l : Fin 2)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hp : p ∈ ((PrimitiveCode.turn (P.turn j)).instanceOf w hw).board.walls) :
    (PrimitiveCode.turn (P.turn i)).actor w hw goal l ≠ (PrimitiveCode.turn (P.turn j)).world w hw p := by
  have hil := hi.1
  have hjl := hj.1
  rcases lt_trichotomy i j with hij | hij | hij
  · have ha := P.turn_actor_at w hw G i hi goal l
    have hb := P.turn_wall_at w hw j p
    rw [P.join_eq w G j hj.1] at hb
    exact P.marks_ne w G i (j+1) (by omega) hj.1 (by omega) 2 (FiniteTools.radius w)
      (by unfold FiniteGeometry.origin FiniteTools.radius; omega) (P.finish_contains w G i (by omega))
      (P.start_contains w G (j+1) hj.1) ha hb
  · subst j
    exact PrimitiveCode.actor_ne_own_wall w hw (.turn (P.turn i)) goal l p hp
  · have ha := P.turn_wall_at w hw j p
    have hb := P.turn_actor_at w hw G i hi goal l
    rw [P.join_eq w G i hi.1] at hb
    exact Ne.symm (P.marks_ne w G j (i+1) (by omega) hi.1 (by omega) (FiniteTools.radius w) 2
      (by unfold FiniteGeometry.origin FiniteTools.radius; omega) (P.finish_contains w G j (by omega))
      (P.start_contains w G (i+1) hi.1) ha hb)

end PushPuzzle.PushS.FiniteRouting.PathSpec
