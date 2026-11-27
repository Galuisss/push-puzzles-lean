/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPrimitiveGeometry

/-! Literal actor and wall clearance at adjacent straight and concave-turn pieces. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteTools.turnWalls

namespace Line

private theorem placed_wall_end (w : ℕ) (atoms : List Atom) (above : Bool)
    (d : Direction) (p q : ℕ × ℕ) (htravel : Travels d p q (span w atoms))
    (hp : p.1 ≤ tileStride w ∧ p.2 ≤ tileStride w)
    (hq : q.1 ≤ tileStride w ∧ q.2 ≤ tileStride w)
    (a : Cell (width w atoms) (height w)) (ha : a ∈ walls w atoms above) :
    Outward d.opposite (along w d q 1) (coordinates ((placement w atoms d p q htravel hp hq).cells a)) := by
  have hb := walls_bounds w atoms above ha
  have hr := rotation_coordinates w atoms d a
  have hx := congrArg Prod.fst hr
  have hy := congrArg Prod.snd hr
  dsimp only at hx hy
  dsimp [coordinates,placement,GridEmbedding.trans,GridEmbedding.translate,GridIsometry.embedding]
  rw [hx,hy]
  have haX := a.1.isLt
  have haY := a.2.isLt
  cases d <;> dsimp [rotatedCoordinates,Outward,along,Travels,offsetX,offsetY,anchor,Direction.opposite] at * <;>
    unfold width height FiniteTools.side FiniteTools.radius padding at * <;> omega

end Line

theorem line_wall_envelope (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hg : LineGood w c.segment)
    (p : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) :
    Outward (segmentDirection c.segment) (Line.along w (segmentDirection c.segment) c.segment.start 0)
        ((PrimitiveCode.line c).world w hw p) ∧
      Outward (segmentDirection c.segment).opposite (Line.along w (segmentDirection c.segment) c.segment.finish 1)
        ((PrimitiveCode.line c).world w hw p) ∧
      ¬SameLane (segmentDirection c.segment) (Line.along w (segmentDirection c.segment) c.segment.start 0)
        ((PrimitiveCode.line c).world w hw p) := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have ht : Travels (segmentDirection c.segment) c.segment.start c.segment.finish (Line.span w atoms) := by
    rw [Line.program_span_of_bound w _ _ hg.2.1]
    exact segment_travels _ hg.1
  change p ∈ (Line.walls w atoms c.above).map (Line.rotation w atoms (segmentDirection c.segment)).cells.toEmbedding at hp
  obtain ⟨a,ha,he⟩ := Finset.mem_map.mp hp
  have hs := Line.placed_wall_side w atoms c.above _ _ _ ht hg.2.2.1 hg.2.2.2 a ha
  have hf := Line.placed_wall_end w atoms c.above _ _ _ ht hg.2.2.1 hg.2.2.2 a ha
  rw [←he]
  exact ⟨hs.1,hf,hs.2⟩

theorem turn_wall_coordinates (w : ℕ) (hw : 2 ≤ w) (c : TurnCode)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hp : p ∈ ((PrimitiveCode.turn c).instanceOf w hw).board.walls) :
    ∃ a : Cell (FiniteTools.side w) (FiniteTools.side w), a ∈ FiniteTools.turnWalls w ∧
      (PrimitiveCode.turn c).world w hw p =
        (Turn.offsetX w c.corner+(Turn.quarterCoordinates w c.incoming
          (if c.outgoing = rightTurn c.incoming then coordinates a
           else (a.1.val,FiniteTools.side w-(a.2.val+1)))).1,
         Turn.offsetY w c.corner+(Turn.quarterCoordinates w c.incoming
          (if c.outgoing = rightTurn c.incoming then coordinates a
           else (a.1.val,FiniteTools.side w-(a.2.val+1)))).2) := by
  change p ∈ (FiniteTools.turnWalls w).map (Turn.orientation w c.incoming c.outgoing).cells.toEmbedding at hp
  obtain ⟨a,ha,he⟩ := Finset.mem_map.mp hp
  refine ⟨a,ha,?_⟩
  have hr := Turn.orientation_coordinates w c.incoming c.outgoing a
  have hx := congrArg Prod.fst hr
  have hy := congrArg Prod.snd hr
  have hex := congrArg (fun z => z.1.val) he
  have hey := congrArg (fun z => z.2.val) he
  dsimp only [coordinates] at hx hy
  change ((Turn.orientation w c.incoming c.outgoing).cells a).1.val = p.1.val at hex
  change ((Turn.orientation w c.incoming c.outgoing).cells a).2.val = p.2.val at hey
  dsimp only [PrimitiveCode.world,PrimitiveCode.offsetX,PrimitiveCode.offsetY]
  rw [←hex,←hey,hx,hy]
  rfl

set_option maxRecDepth 65536 in
/-- The complete incoming and outgoing exposed rays are actual floor of the oriented turn. -/
theorem turn_wall_ne_ray (w : ℕ) (hw : 2 ≤ w) (c : TurnCode)
    (hc : Perpendicular c.incoming c.outgoing) (incoming : Bool) (t : ℕ)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hp : p ∈ ((PrimitiveCode.turn c).instanceOf w hw).board.walls) :
    (PrimitiveCode.turn c).world w hw p ≠
      Line.along w (if incoming then c.incoming.opposite else c.outgoing) c.corner t := by
  obtain ⟨a,ha,he⟩ := turn_wall_coordinates w hw c p hp
  rw [he]
  unfold FiniteTools.turnWalls at ha
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp ha
  have hb := ((FiniteTools.turnRectangle w i).mem_cells _ _ a).mp hi
  intro heq
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  rcases c with ⟨d,e,corner,initial,target⟩
  cases incoming <;> cases d <;> cases e <;> fin_cases i <;>
    simp [Perpendicular,rightTurn,Direction.opposite] at hc <;>
    dsimp [Turn.quarterCoordinates,rightTurn,coordinates,FiniteTools.turnRectangle,Turn.offsetX,
      Turn.offsetY,Line.along,Direction.opposite] at hb hx hy <;>
    simp only [FiniteTools.side,FiniteTools.radius,padding] at hb hx hy <;> omega

/-- Incoming strip walls stop before G and leave F on their open working lane. -/
theorem turn_actor_ne_incoming_wall (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (ht : Perpendicular t.incoming t.outgoing)
    (hd : segmentDirection c.segment = t.incoming)
    (hf : c.segment.finish = advance t.incoming.opposite t.corner 2)
    (goal : Bool) (l : Fin 2)
    (p : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) :
    (PrimitiveCode.turn t).actor w hw goal l ≠ (PrimitiveCode.line c).world w hw p := by
  obtain ⟨hs,he,hn⟩ := line_wall_envelope w hw c hc p hp
  have htravel := segment_travels c.segment hc.1
  have hlen := hc.2.1
  rw [hd,hf] at he htravel
  rw [hd] at hs hn
  intro h
  rw [←h,turn_actor w hw t ht goal l] at hs he hn
  have hi := Bool.toNat_le t.initial
  have hg := Bool.toNat_le t.target
  cases hdi : t.incoming <;> cases hdo : t.outgoing <;> fin_cases l <;>
    simp [hdi,hdo,Perpendicular,rightTurn,Direction.opposite] at ht <;>
    simp only [hdi,hdo] at * <;>
    dsimp [Outward,SameLane,Line.along,Travels,advance,Direction.opposite] at hs he hn htravel <;>
    split_ifs at hs he hn <;> unfold padding at * <;> omega

/-- Outgoing strip walls begin after F and leave G on their open working lane. -/
theorem turn_actor_ne_outgoing_wall (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (ht : Perpendicular t.incoming t.outgoing)
    (hd : segmentDirection c.segment = t.outgoing)
    (hs : c.segment.start = advance t.outgoing t.corner 1)
    (goal : Bool) (l : Fin 2)
    (p : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) :
    (PrimitiveCode.turn t).actor w hw goal l ≠ (PrimitiveCode.line c).world w hw p := by
  obtain ⟨hstart,hend,hn⟩ := line_wall_envelope w hw c hc p hp
  have htravel := segment_travels c.segment hc.1
  have hlen := hc.2.1
  rw [hd,hs] at hstart hn htravel
  intro h
  rw [←h,turn_actor w hw t ht goal l] at hstart hn
  have hi := Bool.toNat_le t.initial
  have hg := Bool.toNat_le t.target
  cases hdi : t.incoming <;> cases hdo : t.outgoing <;> fin_cases l <;>
    simp [hdi,hdo,Perpendicular,rightTurn,Direction.opposite] at ht <;>
    simp only [hdi,hdo] at * <;>
    dsimp [Outward,SameLane,Line.along,Travels,advance,Direction.opposite] at hstart hn htravel <;>
    split_ifs at hstart hn <;> unfold padding at * <;> omega

private theorem incoming_along_ray (w length : ℕ) (d : Direction) (start corner : ℕ × ℕ)
    (htravel : Travels d start (advance d.opposite corner 2) length) (hl : 0 < length)
    (phase : Bool) (position : ℕ) (hp : position+2 ≤ length+phase.toNat) :
    Line.along w d start position = Line.along w d.opposite corner (length+2-position) := by
  have hq := Bool.toNat_le phase
  cases d <;> dsimp [Travels,advance,Direction.opposite,Line.along] at * <;>
    apply Prod.ext <;> unfold padding <;> omega

theorem outgoing_along_ray (w length : ℕ) (d : Direction) (finish corner : ℕ × ℕ)
    (htravel : Travels d (advance d corner 1) finish length) (hl : 0 < length)
    (position : ℕ) (hp : position ≤ length+1) :
    Line.along w d (advance d corner 1) position = Line.along w d corner (position+1) := by
  cases d <;> dsimp [Travels,advance,Direction.opposite,Line.along] at * <;>
    apply Prod.ext <;> unfold padding <;> omega

theorem incoming_line_actor_ray (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (hlast : c.last = false)
    (hd : segmentDirection c.segment = t.incoming)
    (hf : c.segment.finish = advance t.incoming.opposite t.corner 2)
    (goal : Bool) (l : (PrimitiveCode.line c).Labels w) :
    ∃ n, 3 ≤ n ∧ (PrimitiveCode.line c).actor w hw goal l =
      Line.along w t.incoming.opposite t.corner n := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let phase := if goal then c.target else c.initial
  let l' : Line.OwnedLabel w atoms c.first false :=
    ⟨l.val,by simpa only [hlast] using l.property⟩
  have hpos := Line.owned_position_before_last w hw atoms phase c.first l'
  have hlen := Line.program_span_of_bound w (segmentLength c.segment) (c.above != c.desiredSide) hc.2.1
  change Line.position w atoms phase l.val+2 ≤ Line.span w atoms+phase.toNat at hpos
  change Line.span w atoms = segmentLength c.segment at hlen
  rw [hlen] at hpos
  have hphase := Bool.toNat_le phase
  refine ⟨segmentLength c.segment+2-Line.position w atoms phase l.val,by omega,?_⟩
  rw [line_actor w hw c hc goal l,hd]
  have htravel := segment_travels c.segment hc.1
  rw [hd,hf] at htravel
  exact incoming_along_ray w _ t.incoming c.segment.start t.corner htravel (by have h := hc.2.1; omega) phase _ hpos

theorem outgoing_line_actor_ray (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (hfirst : c.first = false)
    (hd : segmentDirection c.segment = t.outgoing)
    (hs : c.segment.start = advance t.outgoing t.corner 1)
    (goal : Bool) (l : (PrimitiveCode.line c).Labels w) :
    ∃ n, 3 ≤ n ∧ (PrimitiveCode.line c).actor w hw goal l =
      Line.along w t.outgoing t.corner n := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let phase := if goal then c.target else c.initial
  let l' : Line.OwnedLabel w atoms false c.last :=
    ⟨l.val,by simpa only [hfirst] using l.property⟩
  have hpos := Line.owned_position_after_first w (segmentLength c.segment) hw
    (c.above != c.desiredSide) phase c.last l'
  have hb := Line.positions_bounds w hw phase atoms (Line.position_mem w atoms phase l.val)
  have hlen := Line.program_span_of_bound w (segmentLength c.segment) (c.above != c.desiredSide) hc.2.1
  change phase.toNat+2 ≤ Line.position w atoms phase l.val at hpos
  change Line.span w atoms = segmentLength c.segment at hlen
  rw [hlen] at hb
  have hphase := Bool.toNat_le phase
  refine ⟨Line.position w atoms phase l.val+1,by omega,?_⟩
  rw [line_actor w hw c hc goal l,hd,hs]
  have htravel := segment_travels c.segment hc.1
  rw [hd,hs] at htravel
  exact outgoing_along_ray w _ t.outgoing c.segment.finish t.corner htravel
    (by have h := hc.2.1; omega) _
    (by change Line.position w atoms phase l.val ≤ segmentLength c.segment+1; omega)

theorem incoming_line_actor_ne_turn_wall (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (ht : Perpendicular t.incoming t.outgoing) (hlast : c.last = false)
    (hd : segmentDirection c.segment = t.incoming)
    (hf : c.segment.finish = advance t.incoming.opposite t.corner 2)
    (goal : Bool) (l : (PrimitiveCode.line c).Labels w)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hp : p ∈ ((PrimitiveCode.turn t).instanceOf w hw).board.walls) :
    (PrimitiveCode.line c).actor w hw goal l ≠ (PrimitiveCode.turn t).world w hw p := by
  obtain ⟨n,_,he⟩ := incoming_line_actor_ray w hw c t hc hlast hd hf goal l
  rw [he]
  exact Ne.symm (turn_wall_ne_ray w hw t ht true n p hp)

theorem outgoing_line_actor_ne_turn_wall (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (ht : Perpendicular t.incoming t.outgoing) (hfirst : c.first = false)
    (hd : segmentDirection c.segment = t.outgoing)
    (hs : c.segment.start = advance t.outgoing t.corner 1)
    (goal : Bool) (l : (PrimitiveCode.line c).Labels w)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hp : p ∈ ((PrimitiveCode.turn t).instanceOf w hw).board.walls) :
    (PrimitiveCode.line c).actor w hw goal l ≠ (PrimitiveCode.turn t).world w hw p := by
  obtain ⟨n,_,he⟩ := outgoing_line_actor_ray w hw c t hc hfirst hd hs goal l
  rw [he]
  exact Ne.symm (turn_wall_ne_ray w hw t ht false n p hp)

private theorem turn_actor_ne_ray_far (w : ℕ) (hw : 2 ≤ w) (t : TurnCode)
    (ht : Perpendicular t.incoming t.outgoing) (incoming : Bool) (n : ℕ) (hn : 3 ≤ n)
    (goal : Bool) (l : Fin 2) :
    (PrimitiveCode.turn t).actor w hw goal l ≠
      Line.along w (if incoming then t.incoming.opposite else t.outgoing) t.corner n := by
  rw [turn_actor w hw t ht goal l]
  have hi := Bool.toNat_le t.initial
  have hg := Bool.toNat_le t.target
  intro heq
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  cases incoming <;> cases hdi : t.incoming <;> cases hdo : t.outgoing <;> fin_cases l <;>
    simp [hdi,hdo,Perpendicular,rightTurn,Direction.opposite] at ht <;>
    simp only [hdi,hdo] at hx hy <;>
    dsimp [Line.along,Direction.opposite] at hx hy <;>
    split_ifs at hx hy <;> unfold padding at hx hy <;> omega

theorem incoming_line_actor_ne_turn_actor (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (ht : Perpendicular t.incoming t.outgoing) (hlast : c.last = false)
    (hd : segmentDirection c.segment = t.incoming)
    (hf : c.segment.finish = advance t.incoming.opposite t.corner 2)
    (goal goal' : Bool) (l : (PrimitiveCode.line c).Labels w) (r : Fin 2) :
    (PrimitiveCode.line c).actor w hw goal l ≠ (PrimitiveCode.turn t).actor w hw goal' r := by
  obtain ⟨n,hn,he⟩ := incoming_line_actor_ray w hw c t hc hlast hd hf goal l
  rw [he]
  exact Ne.symm (turn_actor_ne_ray_far w hw t ht true n hn goal' r)

theorem outgoing_line_actor_ne_turn_actor (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (ht : Perpendicular t.incoming t.outgoing) (hfirst : c.first = false)
    (hd : segmentDirection c.segment = t.outgoing)
    (hs : c.segment.start = advance t.outgoing t.corner 1)
    (goal goal' : Bool) (l : (PrimitiveCode.line c).Labels w) (r : Fin 2) :
    (PrimitiveCode.line c).actor w hw goal l ≠ (PrimitiveCode.turn t).actor w hw goal' r := by
  obtain ⟨n,hn,he⟩ := outgoing_line_actor_ray w hw c t hc hfirst hd hs goal l
  rw [he]
  exact Ne.symm (turn_actor_ne_ray_far w hw t ht false n hn goal' r)

theorem incoming_ray_ne_outgoing_wall (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (ht : Perpendicular t.incoming t.outgoing)
    (hd : segmentDirection c.segment = t.outgoing)
    (hs : c.segment.start = advance t.outgoing t.corner 1) (n : ℕ)
    (p : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) :
    Line.along w t.incoming.opposite t.corner n ≠ (PrimitiveCode.line c).world w hw p := by
  obtain ⟨hstart,_,_⟩ := line_wall_envelope w hw c hc p hp
  have htravel := segment_travels c.segment hc.1
  have hlen := hc.2.1
  rw [hd,hs] at hstart htravel
  intro h
  rw [←h] at hstart
  cases hdi : t.incoming <;> cases hdo : t.outgoing <;>
    simp [hdi,hdo,Perpendicular,rightTurn,Direction.opposite] at ht <;>
    simp only [hdi,hdo] at hstart htravel <;>
    dsimp [Outward,Line.along,Travels,advance,Direction.opposite] at hstart htravel <;>
    unfold padding at hstart <;> omega

theorem outgoing_ray_ne_incoming_wall (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (ht : Perpendicular t.incoming t.outgoing)
    (hd : segmentDirection c.segment = t.incoming)
    (hf : c.segment.finish = advance t.incoming.opposite t.corner 2) (n : ℕ)
    (p : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) :
    Line.along w t.outgoing t.corner n ≠ (PrimitiveCode.line c).world w hw p := by
  obtain ⟨_,hend,_⟩ := line_wall_envelope w hw c hc p hp
  have htravel := segment_travels c.segment hc.1
  have hlen := hc.2.1
  rw [hd,hf] at hend htravel
  intro h
  rw [←h] at hend
  cases hdi : t.incoming <;> cases hdo : t.outgoing <;>
    simp [hdi,hdo,Perpendicular,rightTurn,Direction.opposite] at ht <;>
    simp only [hdi,hdo] at hend htravel <;>
    dsimp [Outward,Line.along,Travels,advance,Direction.opposite] at hend htravel <;>
    unfold padding at hend <;> omega

theorem incoming_line_actor_ne_outgoing_wall (w : ℕ) (hw : 2 ≤ w) (c d : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (hd : LineGood w d.segment) (ht : Perpendicular t.incoming t.outgoing)
    (hlast : c.last = false) (hcdir : segmentDirection c.segment = t.incoming)
    (hcfinish : c.segment.finish = advance t.incoming.opposite t.corner 2)
    (hddir : segmentDirection d.segment = t.outgoing)
    (hdstart : d.segment.start = advance t.outgoing t.corner 1)
    (goal : Bool) (l : (PrimitiveCode.line c).Labels w)
    (p : Cell ((PrimitiveCode.line d).instanceOf w hw).width ((PrimitiveCode.line d).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line d).instanceOf w hw).board.walls) :
    (PrimitiveCode.line c).actor w hw goal l ≠ (PrimitiveCode.line d).world w hw p := by
  obtain ⟨n,_,he⟩ := incoming_line_actor_ray w hw c t hc hlast hcdir hcfinish goal l
  rw [he]
  exact incoming_ray_ne_outgoing_wall w hw d t hd ht hddir hdstart n p hp

theorem outgoing_line_actor_ne_incoming_wall (w : ℕ) (hw : 2 ≤ w) (c d : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (hd : LineGood w d.segment) (ht : Perpendicular t.incoming t.outgoing)
    (hfirst : d.first = false) (hcdir : segmentDirection c.segment = t.incoming)
    (hcfinish : c.segment.finish = advance t.incoming.opposite t.corner 2)
    (hddir : segmentDirection d.segment = t.outgoing)
    (hdstart : d.segment.start = advance t.outgoing t.corner 1)
    (goal : Bool) (l : (PrimitiveCode.line d).Labels w)
    (p : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) :
    (PrimitiveCode.line d).actor w hw goal l ≠ (PrimitiveCode.line c).world w hw p := by
  obtain ⟨n,_,he⟩ := outgoing_line_actor_ray w hw d t hd hfirst hddir hdstart goal l
  rw [he]
  exact outgoing_ray_ne_incoming_wall w hw c t hc ht hcdir hcfinish n p hp

private theorem perpendicular_rays_ne (w : ℕ) (d e : Direction) (hp : Perpendicular d e)
    (corner : ℕ × ℕ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Line.along w d.opposite corner m ≠ Line.along w e corner n := by
  intro heq
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  cases d <;> cases e <;> simp [Perpendicular,rightTurn,Direction.opposite] at hp <;>
    dsimp [Line.along,Direction.opposite] at hx hy <;> unfold padding at hx hy <;> omega

theorem incoming_line_actor_ne_outgoing_actor (w : ℕ) (hw : 2 ≤ w) (c d : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (hd : LineGood w d.segment) (ht : Perpendicular t.incoming t.outgoing)
    (hlast : c.last = false) (hfirst : d.first = false)
    (hcdir : segmentDirection c.segment = t.incoming)
    (hcfinish : c.segment.finish = advance t.incoming.opposite t.corner 2)
    (hddir : segmentDirection d.segment = t.outgoing)
    (hdstart : d.segment.start = advance t.outgoing t.corner 1)
    (goal goal' : Bool) (l : (PrimitiveCode.line c).Labels w) (r : (PrimitiveCode.line d).Labels w) :
    (PrimitiveCode.line c).actor w hw goal l ≠ (PrimitiveCode.line d).actor w hw goal' r := by
  obtain ⟨m,hm,he⟩ := incoming_line_actor_ray w hw c t hc hlast hcdir hcfinish goal l
  obtain ⟨n,hn,hf⟩ := outgoing_line_actor_ray w hw d t hd hfirst hddir hdstart goal' r
  rw [he,hf]
  exact perpendicular_rays_ne w _ _ ht t.corner m n (by omega) (by omega)

end PushPuzzle.PushS.FiniteRouting
