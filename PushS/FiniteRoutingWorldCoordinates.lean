/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionFootprint
public import PushS.FiniteRoutingPathJunctions

/-! Shared literal coordinate formulas for every placed line and turn action. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls Line.program Line.span FiniteTools.side

theorem Line.stockBand_turnSide (w : ℕ) (d e : Direction) (y : ℕ) :
    Line.StockBand w (turnSide d e) y ↔
      if e = rightTurn d then FiniteTools.radius w-w ≤ y ∧ y < FiniteTools.radius w
      else FiniteTools.radius w+1 ≤ y ∧ y < FiniteTools.radius w+w+1 := by
  by_cases h : e = rightTurn d <;> simp [Line.StockBand,turnSide,h]

theorem Line.Action.mem_active (w : ℕ) (atoms : List Line.Atom) (above last : Bool)
    (p : Cell (Line.width w atoms) (Line.height w)) :
    p ∈ Line.Action.active w atoms above last ↔ Line.Action.UsedPoint w atoms above last p ∧
      (FiniteTools.radius w-1 ≤ p.1.val ∧ p.1.val ≤ FiniteTools.radius w+Line.span w atoms+2 ∧
       FiniteTools.radius w-w-1 ≤ p.2.val ∧ p.2.val ≤ FiniteTools.radius w+w+1 ∧ p ∉ Line.walls w atoms above) := by
  exact ⟨fun h => ⟨(Finset.mem_filter.mp h).2,(Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2⟩,
    fun ⟨hu,hb⟩ => Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,hu⟩⟩

theorem Line.placement_coordinates (w : ℕ) (atoms : List Line.Atom) (d : Direction) (start finish : ℕ × ℕ)
    (ht : Travels d start finish (Line.span w atoms))
    (hs : start.1 ≤ tileStride w ∧ start.2 ≤ tileStride w)
    (hf : finish.1 ≤ tileStride w ∧ finish.2 ≤ tileStride w)
    (a : Cell (Line.width w atoms) (Line.height w)) :
    coordinates ((Line.placement w atoms d start finish ht hs hf).cells a) =
      (Line.offsetX w atoms d start+(Line.rotatedCoordinates w atoms d a).1,
       Line.offsetY w atoms d start+(Line.rotatedCoordinates w atoms d a).2) :=
  congrArg (fun xy : ℕ × ℕ => (Line.offsetX w atoms d start+xy.1,Line.offsetY w atoms d start+xy.2))
    (Line.rotation_coordinates w atoms d a)

theorem LineCode.actionWorld_eq (w : ℕ) (hw : 2 ≤ w) (c : LineCode)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w)) :
    let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
    let xy := Line.rotatedCoordinates w atoms (segmentDirection c.segment) p
    c.actionWorld w hw p = (Line.offsetX w atoms (segmentDirection c.segment) c.segment.start+xy.1,
      Line.offsetY w atoms (segmentDirection c.segment) c.segment.start+xy.2) := by
  dsimp only
  have h := Line.rotation_coordinates w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))
    (segmentDirection c.segment) p
  exact congrArg (fun xy : ℕ × ℕ =>
    (Line.offsetX w _ (segmentDirection c.segment) c.segment.start+xy.1,
     Line.offsetY w _ (segmentDirection c.segment) c.segment.start+xy.2)) h

theorem LineCode.wall_world (w : ℕ) (hw : 2 ≤ w) (c : LineCode)
    (q : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hq : q ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) :
    ∃ a : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w),
      a ∈ Line.walls w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above ∧
      (PrimitiveCode.line c).world w hw q = c.actionWorld w hw a := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  change q ∈ (Line.walls w atoms c.above).map (Line.rotation w atoms (segmentDirection c.segment)).cells.toEmbedding at hq
  obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hq
  exact ⟨a,ha,rfl⟩

-- The eight perpendicular placements share these two scalar equations around their common corner.
set_option maxHeartbeats 1000000 in
theorem JunctionContract.action_coordinates (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (e : LineCode)
    (H : JunctionContract w c t e)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w))
    (q : Cell (Line.width w (Line.program w (segmentLength e.segment) (e.above != e.desiredSide))) (Line.height w))
    (he : c.actionWorld w hw p = e.actionWorld w hw q) :
    if t.outgoing = rightTurn t.incoming then
      p.1.val+q.2.val = 2*FiniteTools.radius w+segmentLength c.segment+2 ∧ p.2.val = q.1.val+1
    else p.1.val = segmentLength c.segment+2+q.2.val ∧ p.2.val+q.1.val+1 = 2*FiniteTools.radius w := by
  rw [LineCode.actionWorld_eq,LineCode.actionWorld_eq,H.incoming_direction,H.outgoing_direction,H.outgoing_start] at he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  have hc := segment_travels c.segment H.incoming_good.1
  have hd := segment_travels e.segment H.outgoing_good.1
  rw [H.incoming_direction,H.incoming_finish] at hc
  rw [H.outgoing_direction,H.outgoing_start] at hd
  have hlc := H.incoming_good.2.1
  have hle := H.outgoing_good.2.1
  have hpc := p.1.isLt
  have hpd := p.2.isLt
  have hqc := q.1.isLt
  have hqd := q.2.isLt
  have hspan := Line.program_span_of_bound w _ (c.above != c.desiredSide) hlc
  have hspan' := Line.program_span_of_bound w _ (e.above != e.desiredSide) hle
  have hperp := H.perpendicular
  cases di : t.incoming <;> cases de : t.outgoing <;>
    simp [di,de,Perpendicular,rightTurn,Direction.opposite] at hperp ⊢ <;>
    simp only [di,de] at hc hd hx hy <;>
    dsimp [Line.rotatedCoordinates,Line.offsetX,Line.offsetY,Line.anchor,Travels,advance,Direction.opposite] at hc hd hx hy <;>
    simp only [Line.width,Line.height,FiniteTools.side,FiniteTools.radius,hspan,hspan',padding] at * <;>
    constructor <;> omega

/-- The actual tile coordinate of a canonical turn-action cell. -/
@[expose] def TurnCode.actionWorld (w : ℕ) (hw : 2 ≤ w) (t : TurnCode)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) : ℕ × ℕ :=
  (PrimitiveCode.turn t).world w hw ((Turn.orientation w t.incoming t.outgoing).cells p)

theorem TurnCode.actionWorld_eq (w : ℕ) (hw : 2 ≤ w) (t : TurnCode)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) :
    let xy := Turn.quarterCoordinates w t.incoming
      (if t.outgoing = rightTurn t.incoming then coordinates p else (p.1.val,FiniteTools.side w-(p.2.val+1)))
    t.actionWorld w hw p = (Turn.offsetX w t.corner+xy.1,Turn.offsetY w t.corner+xy.2) :=
  congrArg (fun xy : ℕ × ℕ => (Turn.offsetX w t.corner+xy.1,Turn.offsetY w t.corner+xy.2))
    (Turn.orientation_coordinates w t.incoming t.outgoing p)

/-- Every used cell of one canonical line avoids every wall of another placed line. -/
@[expose] def LineCode.ActionClear (w : ℕ) (hw : 2 ≤ w) (c e : LineCode) : Prop :=
  ∀ (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w)),
    p ∈ Line.Action.active w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last →
    ∀ (q : Cell ((PrimitiveCode.line e).instanceOf w hw).width ((PrimitiveCode.line e).instanceOf w hw).height),
      q ∈ ((PrimitiveCode.line e).instanceOf w hw).board.walls → c.actionWorld w hw p ≠ (PrimitiveCode.line e).world w hw q

/-- The complete canonical turn action avoids every wall of the given placed line. -/
@[expose] def TurnCode.LineClear (w : ℕ) (hw : 2 ≤ w) (t : TurnCode) (c : LineCode) : Prop :=
  ∀ (p : Cell (FiniteTools.side w) (FiniteTools.side w)), p ∈ FiniteTools.turnActive w →
    ∀ (q : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height),
      q ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls → t.actionWorld w hw p ≠ (PrimitiveCode.line c).world w hw q

end PushPuzzle.PushS.FiniteRouting
