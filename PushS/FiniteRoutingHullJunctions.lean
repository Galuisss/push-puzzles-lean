/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingTravelHull
public import PushS.FiniteRoutingCollinear

/-! Complete normal-travel intervals of adjacent emitted path pieces are disjoint. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

def HullsApart (w : ℕ) (hw : 2 ≤ w) (c d : PrimitiveCode) : Prop :=
  ∀ (l : c.Labels w) (r : d.Labels w) (a b : ℕ × ℕ),
    ActorHull w hw c l a → ActorHull w hw d r b → a ≠ b

private theorem hull_nearby (margin : ℕ) (a b p center : ℕ × ℕ)
    (ha : Nearby margin a center) (hb : Nearby margin b center) (hp : Hull a b p) :
    Nearby margin p center := by
  dsimp [Hull,Nearby] at *
  omega

theorem line_hull_footprint (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (hf : c.first = false) (l : (PrimitiveCode.line c).Labels w) (a : ℕ × ℕ) (ha : ActorHull w hw (.line c) l a) :
    ∃ u, c.segment.Contains u ∧ Nearby 1 a (padding w+u.1,padding w+u.2) := by
  obtain ⟨n,_,hn,_,he⟩ := line_hull_bounds w hw c hc hf l a ha
  obtain ⟨u,hu,hnear⟩ := c.row_footprint w hw hc n hn
  rw [LineCode.rowWorld_eq] at hnear
  exact ⟨u,hu,he ▸ hnear⟩

theorem turn_hull_footprint (w : ℕ) (hw : 2 ≤ w) (c : TurnCode) (hc : Perpendicular c.incoming c.outgoing)
    (l : Fin 2) (a : ℕ × ℕ) (ha : ActorHull w hw (.turn c) l a) :
    Nearby 2 a (padding w+c.corner.1,padding w+c.corner.2) :=
  hull_nearby 2 _ _ _ _ (turn_actor_footprint w hw c hc false l) (turn_actor_footprint w hw c hc true l) ha

theorem collinear_hulls_apart (w : ℕ) (hw : 2 ≤ w) (c e : LineCode) (H : CollinearContract w c e)
    (hf : c.first = false) : HullsApart w hw (.line c) (.line e) := by
  intro l r a b ha hb he
  obtain ⟨n,_,hn,_,hea⟩ := line_hull_bounds w hw c H.first_good hf l a ha
  obtain ⟨m,hm,hm',_,heb⟩ := line_hull_bounds w hw e H.next_good H.next_first r b hb
  have ht := segment_travels c.segment H.first_good.1
  have ht' := segment_travels e.segment H.next_good.1
  rw [←H.directions,←H.joined] at ht'
  rw [hea,heb,←H.directions,←H.joined] at he
  cases hd : segmentDirection c.segment <;> simp only [hd] at ht ht' he <;>
    dsimp [Line.along,Travels] at ht ht' he <;> unfold padding at * <;>
    have hx := congrArg Prod.fst he <;> have hy := congrArg Prod.snd he <;> dsimp only at hx hy <;> omega

private theorem turn_hull_ne_ray_far (w : ℕ) (hw : 2 ≤ w) (c : TurnCode)
    (hc : Perpendicular c.incoming c.outgoing) (incoming : Bool) (n : ℕ) (hn : 3 ≤ n)
    (l : Fin 2) (a : ℕ × ℕ) (ha : ActorHull w hw (.turn c) l a) :
    a ≠ Line.along w (if incoming then c.incoming.opposite else c.outgoing) c.corner n := by
  change Hull ((PrimitiveCode.turn c).actor w hw false l) ((PrimitiveCode.turn c).actor w hw true l) a at ha
  rw [turn_actor w hw c hc false l,turn_actor w hw c hc true l] at ha
  have hi := Bool.toNat_le c.initial
  have ht := Bool.toNat_le c.target
  intro heq
  rw [heq] at ha
  cases incoming <;> fin_cases l <;> cases hd : c.incoming <;> cases he : c.outgoing <;>
    simp [hd,he,Perpendicular,rightTurn,Direction.opposite] at hc <;>
    simp only [hd,he] at ha <;>
    dsimp [Hull,Line.along,Direction.opposite] at ha <;> unfold padding at ha <;> omega

private theorem incoming_hull_ray (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (hf : c.first = false) (hl : c.last = false)
    (hd : segmentDirection c.segment = t.incoming)
    (he : c.segment.finish = advance t.incoming.opposite t.corner 2)
    (l : (PrimitiveCode.line c).Labels w) (a : ℕ × ℕ) (ha : ActorHull w hw (.line c) l a) :
    ∃ n, 3 ≤ n ∧ a = Line.along w t.incoming.opposite t.corner n := by
  obtain ⟨m,hm,hm',hlast,hp⟩ := line_hull_bounds w hw c hc hf l a ha
  have hlast' := hlast hl
  refine ⟨segmentLength c.segment+2-m,by omega,?_⟩
  have hh := c.incoming_row_ray w hw t hc hd he m hm'
  rw [LineCode.rowWorld_eq] at hh
  exact hp.trans hh

private theorem outgoing_hull_ray (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (hf : c.first = false) (hd : segmentDirection c.segment = t.outgoing)
    (he : c.segment.start = advance t.outgoing t.corner 1)
    (l : (PrimitiveCode.line c).Labels w) (a : ℕ × ℕ) (ha : ActorHull w hw (.line c) l a) :
    ∃ n, 3 ≤ n ∧ a = Line.along w t.outgoing t.corner n := by
  obtain ⟨m,hm,hm',_,hp⟩ := line_hull_bounds w hw c hc hf l a ha
  refine ⟨m+1,by omega,?_⟩
  have hh := c.outgoing_row_ray w hw t hc hd he m hm'
  rw [LineCode.rowWorld_eq] at hh
  exact hp.trans hh

theorem incoming_turn_hulls_apart (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (e : LineCode)
    (H : JunctionContract w c t e) (hf : c.first = false) : HullsApart w hw (.line c) (.turn t) := by
  intro l r a b ha hb
  obtain ⟨n,hn,he⟩ := incoming_hull_ray w hw c t H.incoming_good hf H.incoming_last
    H.incoming_direction H.incoming_finish l a ha
  rw [he]
  exact Ne.symm (turn_hull_ne_ray_far w hw t H.perpendicular true n hn r b hb)

theorem outgoing_turn_hulls_apart (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (e : LineCode)
    (H : JunctionContract w c t e) : HullsApart w hw (.line e) (.turn t) := by
  intro l r a b ha hb
  obtain ⟨n,hn,he⟩ := outgoing_hull_ray w hw e t H.outgoing_good H.outgoing_first H.outgoing_direction H.outgoing_start l a ha
  rw [he]
  exact Ne.symm (turn_hull_ne_ray_far w hw t H.perpendicular false n hn r b hb)

theorem perpendicular_hull_lines_apart (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (e : LineCode)
    (H : JunctionContract w c t e) (hf : c.first = false) : HullsApart w hw (.line c) (.line e) := by
  intro l r a b ha hb
  obtain ⟨n,hn,he⟩ := incoming_hull_ray w hw c t H.incoming_good hf H.incoming_last H.incoming_direction H.incoming_finish l a ha
  obtain ⟨m,hm,he'⟩ := outgoing_hull_ray w hw e t H.outgoing_good H.outgoing_first H.outgoing_direction H.outgoing_start r b hb
  rw [he,he']
  intro h
  have ht := H.perpendicular
  cases hd : t.incoming <;> cases ho : t.outgoing <;> simp [hd,ho,Perpendicular,rightTurn,Direction.opposite] at ht <;>
    simp only [hd,ho] at h <;>
    dsimp [Line.along,Direction.opposite] at h <;> unfold padding at h <;>
    have hx := congrArg Prod.fst h <;> have hy := congrArg Prod.snd h <;> dsimp only at hx hy <;> omega

end PushPuzzle.PushS.FiniteRouting
