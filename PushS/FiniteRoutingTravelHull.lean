/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingGateRows
public import PushS.FiniteRoutingLineCut

/-! Literal closed normal-travel intervals, retaining the flip middle box's full three-cell motion. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

def Hull (a b p : ℕ × ℕ) : Prop :=
  min a.1 b.1 ≤ p.1 ∧ p.1 ≤ max a.1 b.1 ∧ min a.2 b.2 ≤ p.2 ∧ p.2 ≤ max a.2 b.2

def ActorHull (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) (l : c.Labels w) (p : ℕ × ℕ) : Prop :=
  Hull (c.actor w hw false l) (c.actor w hw true l) p

theorem actor_hull_cell (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) (l : c.Labels w)
    (a : ℕ × ℕ) (ha : ActorHull w hw c l a) :
    ∃ p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height, c.world w hw p = a := by
  have hsx := ((c.matching w hw).source l).1.isLt
  have hsy := ((c.matching w hw).source l).2.isLt
  have htx := ((c.matching w hw).target l).1.isLt
  have hty := ((c.matching w hw).target l).2.isLt
  change Hull
    (c.offsetX w+((c.matching w hw).source l).1.val,c.offsetY w+((c.matching w hw).source l).2.val)
    (c.offsetX w+((c.matching w hw).target l).1.val,c.offsetY w+((c.matching w hw).target l).2.val) a at ha
  dsimp [Hull] at ha
  let p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height :=
    (⟨a.1-c.offsetX w,by omega⟩,⟨a.2-c.offsetY w,by omega⟩)
  refine ⟨p,?_⟩
  apply Prod.ext <;> dsimp [PrimitiveCode.world,p] <;> omega

private theorem along_hull (w : ℕ) (d : Direction) (a b : ℕ × ℕ) (length : ℕ)
    (ht : Travels d a b length) (n m : ℕ) (hn : n ≤ length+1) (hm : m ≤ length+1)
    (p : ℕ × ℕ) (hp : Hull (Line.along w d a n) (Line.along w d a m) p) :
    ∃ t, min n m ≤ t ∧ t ≤ max n m ∧ p = Line.along w d a t := by
  cases d
  · refine ⟨padding w+a.2-p.2,?_,?_,?_⟩
    all_goals dsimp [Hull,Line.along,Travels] at hp ht ⊢; unfold padding at *
    · omega
    · omega
    · apply Prod.ext <;> omega
  · refine ⟨p.1-(padding w+a.1),?_,?_,?_⟩
    all_goals dsimp [Hull,Line.along,Travels] at hp ht ⊢; unfold padding at *
    · omega
    · omega
    · apply Prod.ext <;> omega
  · refine ⟨p.2-(padding w+a.2),?_,?_,?_⟩
    all_goals dsimp [Hull,Line.along,Travels] at hp ht ⊢; unfold padding at *
    · omega
    · omega
    · apply Prod.ext <;> omega
  · refine ⟨padding w+a.1-p.1,?_,?_,?_⟩
    all_goals dsimp [Hull,Line.along,Travels] at hp ht ⊢; unfold padding at *
    · omega
    · omega
    · apply Prod.ext <;> omega

theorem line_hull_bounds (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (hf : c.first = false) (l : (PrimitiveCode.line c).Labels w) (p : ℕ × ℕ)
    (hp : ActorHull w hw (.line c) l p) :
    ∃ n, 2 ≤ n ∧ n ≤ segmentLength c.segment+1 ∧
      (c.last = false → n+2 ≤ segmentLength c.segment+1) ∧
      p = Line.along w (segmentDirection c.segment) c.segment.start n := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have hlen : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  have hbound (phase : Bool) : 2 ≤ Line.position w atoms phase l.val ∧
      Line.position w atoms phase l.val ≤ segmentLength c.segment+1 ∧
      (c.last = false → Line.position w atoms phase l.val+2 ≤ segmentLength c.segment+1) := by
    let l' : Line.OwnedLabel w atoms false c.last := ⟨l.val,by simpa only [hf] using l.property⟩
    have hlo := Line.owned_position_after_first w (segmentLength c.segment) hw
      (c.above != c.desiredSide) phase c.last l'
    have hhi := Line.positions_bounds w hw phase atoms (Line.position_mem w atoms phase l.val)
    have hphase := Bool.toNat_le phase
    change phase.toNat+2 ≤ Line.position w atoms phase l.val at hlo
    rw [hlen] at hhi
    refine ⟨by omega,by omega,?_⟩
    intro hl
    let l'' : Line.OwnedLabel w atoms c.first false := ⟨l.val,by simpa only [hl] using l.property⟩
    have hb := Line.owned_position_before_last w hw atoms phase c.first l''
    change Line.position w atoms phase l.val+2 ≤ Line.span w atoms+phase.toNat at hb
    rw [hlen] at hb
    omega
  have ha := hbound c.initial
  have hb := hbound c.target
  change Hull ((PrimitiveCode.line c).actor w hw false l) ((PrimitiveCode.line c).actor w hw true l) p at hp
  rw [line_actor w hw c hc false l,line_actor w hw c hc true l] at hp
  obtain ⟨n,hn,hn',he⟩ := along_hull w _ c.segment.start c.segment.finish (segmentLength c.segment)
    (segment_travels c.segment hc.1) _ _ ha.2.1 hb.2.1 p hp
  refine ⟨n,?_,?_,?_,he⟩
  · omega
  · omega
  · intro hl
    have ha' := ha.2.2 hl
    have hb' := hb.2.2 hl
    omega

end PushPuzzle.PushS.FiniteRouting
