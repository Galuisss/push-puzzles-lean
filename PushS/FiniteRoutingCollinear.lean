/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingJunctions

/-! Literal ownership and wall clearance across the collinear adapter-to-annulus seam. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls

theorem collinear_actor_ne_wall (w : ℕ) (hw : 2 ≤ w) (c d : LineCode)
    (hc : LineGood w c.segment) (hd : LineGood w d.segment)
    (hdir : segmentDirection c.segment = segmentDirection d.segment)
    (hjoin : c.segment.finish = d.segment.start) (goal : Bool)
    (l : (PrimitiveCode.line c).Labels w)
    (p : Cell ((PrimitiveCode.line d).instanceOf w hw).width ((PrimitiveCode.line d).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line d).instanceOf w hw).board.walls) :
    (PrimitiveCode.line c).actor w hw goal l ≠ (PrimitiveCode.line d).world w hw p := by
  obtain ⟨_,_,hn⟩ := line_wall_envelope w hw d hd p hp
  have ht := segment_travels c.segment hc.1
  intro he
  rw [←he,line_actor w hw c hc goal l,←hdir,←hjoin] at hn
  cases hdi : segmentDirection c.segment <;> simp only [hdi] at ht hn <;>
    dsimp [Travels,SameLane,Line.along] at ht hn <;> omega

theorem collinear_next_actor_ne_wall (w : ℕ) (hw : 2 ≤ w) (c d : LineCode)
    (hc : LineGood w c.segment) (hd : LineGood w d.segment)
    (hdir : segmentDirection c.segment = segmentDirection d.segment)
    (hjoin : c.segment.finish = d.segment.start) (goal : Bool)
    (l : (PrimitiveCode.line d).Labels w)
    (p : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) :
    (PrimitiveCode.line d).actor w hw goal l ≠ (PrimitiveCode.line c).world w hw p := by
  obtain ⟨_,_,hn⟩ := line_wall_envelope w hw c hc p hp
  have ht := segment_travels c.segment hc.1
  intro he
  rw [←he,line_actor w hw d hd goal l,←hdir,←hjoin] at hn
  cases hdi : segmentDirection c.segment <;> simp only [hdi] at ht hn <;>
    dsimp [Travels,SameLane,Line.along] at ht hn <;> omega

theorem collinear_actor_ne_actor (w : ℕ) (hw : 2 ≤ w) (c d : LineCode)
    (hc : LineGood w c.segment) (hd : LineGood w d.segment) (hfirst : d.first = false)
    (hdir : segmentDirection c.segment = segmentDirection d.segment)
    (hjoin : c.segment.finish = d.segment.start) (goal goal' : Bool)
    (l : (PrimitiveCode.line c).Labels w) (r : (PrimitiveCode.line d).Labels w) :
    (PrimitiveCode.line c).actor w hw goal l ≠ (PrimitiveCode.line d).actor w hw goal' r := by
  let ca := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let da := Line.program w (segmentLength d.segment) (d.above != d.desiredSide)
  let cp := if goal then c.target else c.initial
  let dp := if goal' then d.target else d.initial
  let r' : Line.OwnedLabel w da false d.last := ⟨r.val,by simpa only [hfirst] using r.property⟩
  have hca := Line.positions_bounds w hw cp ca (Line.position_mem w ca cp l.val)
  have hda := Line.positions_bounds w hw dp da (Line.position_mem w da dp r.val)
  have hfirstpos := Line.owned_position_after_first w (segmentLength d.segment) hw
    (d.above != d.desiredSide) dp d.last r'
  have hclen := Line.program_span_of_bound w _ (c.above != c.desiredSide) hc.2.1
  have hdlen := Line.program_span_of_bound w _ (d.above != d.desiredSide) hd.2.1
  change Line.span w ca = segmentLength c.segment at hclen
  change Line.span w da = segmentLength d.segment at hdlen
  change dp.toNat+2 ≤ Line.position w da dp r.val at hfirstpos
  rw [hclen] at hca
  rw [hdlen] at hda
  have hcp := Bool.toNat_le cp
  have hdp := Bool.toNat_le dp
  have hct := segment_travels c.segment hc.1
  have hdt := segment_travels d.segment hd.1
  rw [←hdir,←hjoin] at hdt
  rw [line_actor w hw c hc goal l,line_actor w hw d hd goal' r,←hdir,←hjoin]
  change Line.along w (segmentDirection c.segment) c.segment.start (Line.position w ca cp l.val) ≠
    Line.along w (segmentDirection c.segment) c.segment.finish (Line.position w da dp r.val)
  intro he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  cases hdi : segmentDirection c.segment <;> simp only [hdi] at hct hdt hx hy <;>
    dsimp [Travels,Line.along] at hct hdt hx hy <;> unfold padding at hx hy <;> omega

end PushPuzzle.PushS.FiniteRouting
