/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPathLayout
public import PushS.FiniteRoutingLineCut

/-! Normal line inventories and coherent collinear seams retain an empty cell between boxes. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side

theorem adjacent_coordinates {W H : ℕ} {d : Direction} {p q : Cell W H}
    (h : Adjacent d p q) : Travels d (coordinates p) (coordinates q) 1 := by
  cases d <;> simp only [Adjacent,Travels,coordinates] at *
  all_goals constructor <;> omega

theorem travels_one_nearby {d : Direction} {p q : ℕ × ℕ} (h : Travels d p q 1) : Nearby 1 p q := by
  cases d <;> dsimp [Travels,Nearby] at * <;> omega

theorem travels_one_reverse {d : Direction} {p q : ℕ × ℕ} (h : Travels d p q 1) :
    Travels d.opposite q p 1 := by
  cases d <;> simpa only [Direction.opposite,Travels,eq_comm] using h

theorem shift_travels_iff (a : ℕ × ℕ) (d : Direction) (p q : ℕ × ℕ) :
    Travels d (a.1+p.1,a.2+p.2) (a.1+q.1,a.2+q.2) 1 ↔ Travels d p q 1 := by
  cases d <;> dsimp [Travels] <;> omega

theorem line_actor_sparse (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (goal : Bool) (l r : (PrimitiveCode.line c).Labels w) (d : Direction) :
    ¬Travels d ((PrimitiveCode.line c).actor w hw goal l)
      ((PrimitiveCode.line c).actor w hw goal r) 1 := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let phase := if goal then c.target else c.initial
  have hb := Line.positions_bounds w hw phase atoms (Line.position_mem w atoms phase l.val)
  have hb' := Line.positions_bounds w hw phase atoms (Line.position_mem w atoms phase r.val)
  have hlen := Line.program_span_of_bound w _ (c.above != c.desiredSide) hc.2.1
  change Line.span w atoms = segmentLength c.segment at hlen
  rw [hlen] at hb hb'
  have hp := Bool.toNat_le phase
  have ht := segment_travels c.segment hc.1
  rw [line_actor w hw c hc goal l,line_actor w hw c hc goal r]
  change ¬Travels d
    (Line.along w (segmentDirection c.segment) c.segment.start (Line.position w atoms phase l.val))
    (Line.along w (segmentDirection c.segment) c.segment.start (Line.position w atoms phase r.val)) 1
  intro ha
  rcases lt_trichotomy l.val.val r.val.val with ho | he | ho
  · have hg := Line.position_gap w hw atoms phase l.val r.val ho
    cases hdir : segmentDirection c.segment <;> simp only [hdir] at ht ha <;>
      cases d <;> dsimp [Travels,Line.along] at ht ha <;> unfold padding at * <;> omega
  · have hl : l = r := Subtype.ext (Fin.ext he)
    subst r
    cases d <;> dsimp [Travels] at ha <;> omega
  · have hg := Line.position_gap w hw atoms phase r.val l.val ho
    cases hdir : segmentDirection c.segment <;> simp only [hdir] at ht ha <;>
      cases d <;> dsimp [Travels,Line.along] at ht ha <;> unfold padding at * <;> omega

theorem collinear_actor_sparse (w : ℕ) (hw : 2 ≤ w) (c e : LineCode)
    (hc : LineGood w c.segment) (he : LineGood w e.segment) (hfirst : e.first = false)
    (hdir : segmentDirection c.segment = segmentDirection e.segment)
    (hjoin : c.segment.finish = e.segment.start)
    (hi : c.initial = e.initial) (hg : c.target = e.target) (goal : Bool)
    (l : (PrimitiveCode.line c).Labels w) (r : (PrimitiveCode.line e).Labels w) (d : Direction) :
    ¬Travels d ((PrimitiveCode.line c).actor w hw goal l)
      ((PrimitiveCode.line e).actor w hw goal r) 1 := by
  let ca := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let ea := Line.program w (segmentLength e.segment) (e.above != e.desiredSide)
  let phase := if goal then c.target else c.initial
  have hphase : (if goal then e.target else e.initial) = phase := by cases goal <;> simp_all [phase]
  let r' : Line.OwnedLabel w ea false e.last := ⟨r.val,by simpa only [hfirst] using r.property⟩
  have hcpos := Line.positions_bounds w hw phase ca (Line.position_mem w ca phase l.val)
  have hepos := Line.positions_bounds w hw phase ea (Line.position_mem w ea phase r.val)
  have hfirstpos := Line.owned_position_after_first w (segmentLength e.segment) hw
    (e.above != e.desiredSide) phase e.last r'
  have hclen := Line.program_span_of_bound w _ (c.above != c.desiredSide) hc.2.1
  have helen := Line.program_span_of_bound w _ (e.above != e.desiredSide) he.2.1
  change Line.span w ca = segmentLength c.segment at hclen
  change Line.span w ea = segmentLength e.segment at helen
  change phase.toNat+2 ≤ Line.position w ea phase r.val at hfirstpos
  rw [hclen] at hcpos
  rw [helen] at hepos
  have hcp := Bool.toNat_le phase
  have hct := segment_travels c.segment hc.1
  have het := segment_travels e.segment he.1
  rw [←hdir,←hjoin] at het
  rw [line_actor w hw c hc goal l,line_actor w hw e he goal r,←hdir,←hjoin,hphase]
  change ¬Travels d
    (Line.along w (segmentDirection c.segment) c.segment.start (Line.position w ca phase l.val))
    (Line.along w (segmentDirection c.segment) c.segment.finish (Line.position w ea phase r.val)) 1
  intro ha
  cases hdi : segmentDirection c.segment <;> simp only [hdi] at hct het ha <;>
    cases d <;> dsimp [Travels,Line.along] at hct het ha <;> unfold padding at * <;> omega

theorem turn_actor_sparse (w : ℕ) (hw : 2 ≤ w) (c : TurnCode)
    (hc : Perpendicular c.incoming c.outgoing) (goal : Bool) (l r : Fin 2) (d : Direction) :
    ¬Travels d ((PrimitiveCode.turn c).actor w hw goal l)
      ((PrimitiveCode.turn c).actor w hw goal r) 1 := by
  rw [turn_actor w hw c hc goal l,turn_actor w hw c hc goal r]
  have hi := Bool.toNat_le c.initial
  have ht := Bool.toNat_le c.target
  intro ha
  cases hdi : c.incoming <;> cases hdo : c.outgoing <;>
    simp only [hdi,hdo] at hc ha <;>
    simp [Perpendicular,rightTurn,Direction.opposite] at hc
  all_goals fin_cases l <;> fin_cases r <;> cases goal <;> cases d <;>
    simp only [↓reduceIte] at ha <;>
    dsimp [Travels,Line.along,Direction.opposite] at ha <;> unfold padding at * <;> omega

theorem perpendicular_rays_sparse (w : ℕ) (d e : Direction) (hp : Perpendicular d e)
    (corner : ℕ × ℕ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (face : Direction) :
    ¬Travels face (Line.along w d.opposite corner m) (Line.along w e corner n) 1 := by
  intro ha
  cases d <;> cases e <;> simp [Perpendicular,rightTurn,Direction.opposite] at hp
  all_goals cases face <;> dsimp [Travels,Line.along,Direction.opposite] at ha <;> unfold padding at * <;> omega

theorem incoming_line_turn_sparse (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (ht : Perpendicular t.incoming t.outgoing)
    (hlast : c.last = false) (hd : segmentDirection c.segment = t.incoming)
    (hf : c.segment.finish = advance t.incoming.opposite t.corner 2)
    (hi : c.initial = t.initial) (hg : c.target = t.target) (goal : Bool)
    (l : (PrimitiveCode.line c).Labels w) (r : Fin 2) (d : Direction) :
    ¬Travels d ((PrimitiveCode.line c).actor w hw goal l) ((PrimitiveCode.turn t).actor w hw goal r) 1 := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let phase := if goal then c.target else c.initial
  have heq : (if goal then t.target else t.initial) = phase := by cases goal <;> simp_all [phase]
  let l' : Line.OwnedLabel w atoms c.first false := ⟨l.val,by simpa only [hlast] using l.property⟩
  have hpos := Line.owned_position_before_last w hw atoms phase c.first l'
  have hlen := Line.program_span_of_bound w _ (c.above != c.desiredSide) hc.2.1
  change Line.span w atoms = segmentLength c.segment at hlen
  change Line.position w atoms phase l.val+2 ≤ Line.span w atoms+phase.toNat at hpos
  rw [hlen] at hpos
  have hp := Bool.toNat_le phase
  have htravel := segment_travels c.segment hc.1
  rw [hd,hf] at htravel
  rw [line_actor w hw c hc goal l,turn_actor w hw t ht goal r,hd,heq]
  change ¬Travels d (Line.along w t.incoming c.segment.start (Line.position w atoms phase l.val))
    (if r = 0 then Line.along w t.incoming.opposite t.corner (2-phase.toNat)
      else Line.along w t.outgoing t.corner (1+phase.toNat)) 1
  intro ha
  cases hdi : t.incoming <;> cases hdo : t.outgoing <;>
    simp only [hdi,hdo] at ht htravel ha <;>
    simp [Perpendicular,rightTurn,Direction.opposite] at ht
  all_goals fin_cases r <;> cases d <;>
    dsimp [Travels,Line.along,advance,Direction.opposite] at ha htravel <;> unfold padding at * <;> omega

theorem outgoing_line_turn_sparse (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (ht : Perpendicular t.incoming t.outgoing)
    (hfirst : c.first = false) (hd : segmentDirection c.segment = t.outgoing)
    (hs : c.segment.start = advance t.outgoing t.corner 1)
    (hi : c.initial = t.initial) (hg : c.target = t.target) (goal : Bool)
    (l : (PrimitiveCode.line c).Labels w) (r : Fin 2) (d : Direction) :
    ¬Travels d ((PrimitiveCode.line c).actor w hw goal l) ((PrimitiveCode.turn t).actor w hw goal r) 1 := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let phase := if goal then c.target else c.initial
  have heq : (if goal then t.target else t.initial) = phase := by cases goal <;> simp_all [phase]
  let l' : Line.OwnedLabel w atoms false c.last := ⟨l.val,by simpa only [hfirst] using l.property⟩
  have hpos := Line.owned_position_after_first w (segmentLength c.segment) hw
    (c.above != c.desiredSide) phase c.last l'
  have hb := Line.positions_bounds w hw phase atoms (Line.position_mem w atoms phase l.val)
  have hlen := Line.program_span_of_bound w _ (c.above != c.desiredSide) hc.2.1
  change Line.span w atoms = segmentLength c.segment at hlen
  change phase.toNat+2 ≤ Line.position w atoms phase l.val at hpos
  rw [hlen] at hb
  have hp := Bool.toNat_le phase
  have htravel := segment_travels c.segment hc.1
  rw [hd,hs] at htravel
  rw [line_actor w hw c hc goal l,turn_actor w hw t ht goal r,hd,hs,heq]
  change ¬Travels d (Line.along w t.outgoing (advance t.outgoing t.corner 1)
      (Line.position w atoms phase l.val))
    (if r = 0 then Line.along w t.incoming.opposite t.corner (2-phase.toNat)
      else Line.along w t.outgoing t.corner (1+phase.toNat)) 1
  intro ha
  cases hdi : t.incoming <;> cases hdo : t.outgoing <;>
    simp only [hdi,hdo] at ht htravel ha <;>
    simp [Perpendicular,rightTurn,Direction.opposite] at ht
  all_goals fin_cases r <;> cases d <;>
    dsimp [Travels,Line.along,advance,Direction.opposite] at ha htravel <;> unfold padding at * <;> omega

end PushPuzzle.PushS.FiniteRouting
