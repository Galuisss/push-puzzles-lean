/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPortCoordinates
public import PushS.FiniteRoutingActionEndBand

/-! Complementary source ports preserve the full strict action footprint across their actual seam. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls Line.program Line.span FiniteTools.side

theorem LineCode.exitSide_eq (w : ℕ) (c : LineCode) :
    Line.exitSide c.above (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) = c.desiredSide := by
  cases c.above <;> cases c.desiredSide <;> simp [Line.program_exitSide]

namespace Line.Action

private theorem first_not_stock (w length : ℕ) (switch above last : Bool)
    (p : Cell (Line.width w (Line.program w length switch)) (Line.height w))
    (hp : p ∈ active w (Line.program w length switch) above last)
    (hx : p.1.val < FiniteTools.radius w+2*Line.buffer w+2) : ¬Line.StockBand w above p.2.val := by
  have hu := (Finset.mem_filter.mp hp).2
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hpx : FiniteTools.radius w ≤ p.1.val := by
    change UsedPoint w (Line.program w length switch) above last p at hu
    rcases hu with hu | hu | hu <;> omega
  exact fun hy => hb.2.2.2.2 (Line.program_first_stock_wall w length switch above p hpx hx hy)

private theorem last_not_stock (w length : ℕ) (switch above last : Bool)
    (p : Cell (Line.width w (Line.program w length switch)) (Line.height w))
    (hp : p ∈ active w (Line.program w length switch) above last)
    (hx : FiniteTools.radius w+Line.span w (Line.program w length switch) ≤ p.1.val+2*Line.buffer w) :
    ¬Line.StockBand w (Line.exitSide above (Line.program w length switch)) p.2.val := by
  intro hy
  have hu := (Finset.mem_filter.mp hp).2
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hmax : p.1.val ≤ FiniteTools.radius w+Line.span w (Line.program w length switch) := by
    change UsedPoint w (Line.program w length switch) above last p at hu
    rcases hu with hu | hu | hu
    · cases hside : Line.exitSide above (Line.program w length switch) <;>
        simp only [hside,Line.StockBand,Bool.false_eq_true,↓reduceIte] at hy <;> omega
    · exact hu.2
    · cases hside : Line.exitSide above (Line.program w length switch) <;>
        simp only [hside,Line.StockBand,Line.Exposed,Bool.false_eq_true,↓reduceIte] at hy hu <;> omega
  exact hb.2.2.2.2 (Line.program_last_stock_wall w length switch above p hx (by omega) hy)

end Line.Action

private structure SeamState (w : ℕ) (hw : 2 ≤ w) (pos other : ℕ × ℕ) (face : Direction) (c e : LineCode) where
  cgood : LineGood w c.segment
  egood : LineGood w e.segment
  p : c.ActionCell w
  active : p ∈ Line.Action.active w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last
  a : Cell (Line.width w (Line.program w (segmentLength e.segment) (e.above != e.desiredSide))) (Line.height w)
  wall : a ∈ Line.walls w (Line.program w (segmentLength e.segment) (e.above != e.desiredSide)) e.above
  along : (portCoordinates w pos face (macroShift w pos (c.actionWorld w hw p))).1+
    (portCoordinates w other face.opposite (macroShift w other (e.actionWorld w hw a))).1 = 0
  across : (portCoordinates w pos face (macroShift w pos (c.actionWorld w hw p))).2+
    (portCoordinates w other face.opposite (macroShift w other (e.actionWorld w hw a))).2 = 0
  active_bounds : FiniteTools.radius w-1 ≤ p.1.val ∧
    p.1.val ≤ FiniteTools.radius w+Line.span w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))+2 ∧
    FiniteTools.radius w-w-1 ≤ p.2.val ∧ p.2.val ≤ FiniteTools.radius w+w+1 ∧
    p ∉ Line.walls w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above
  c_length : Line.span w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) = segmentLength c.segment
  e_length : Line.span w (Line.program w (segmentLength e.segment) (e.above != e.desiredSide)) = segmentLength e.segment
  wall_bounds : FiniteTools.radius w ≤ a.1.val ∧
    a.1.val < FiniteTools.radius w+Line.span w (Line.program w (segmentLength e.segment) (e.above != e.desiredSide))+2 ∧
    FiniteTools.radius w-w ≤ a.2.val ∧ a.2.val < FiniteTools.radius w+w+1

variable {w : ℕ} {hw : 2 ≤ w} {pos other : ℕ × ℕ} {face : Direction} {c e : LineCode}

private theorem end_end_impossible (S : SeamState w hw pos other face c e) (incoming : Bool)
    (hcd : segmentDirection c.segment = face)
    (hcf : c.segment.finish = advance face.opposite (boundaryPoint w face) incoming.toNat)
    (hcs : c.desiredSide = incoming) (hed : segmentDirection e.segment = face.opposite)
    (hef : e.segment.finish = advance face.opposite.opposite (boundaryPoint w face.opposite) (!incoming).toNat)
    (hes : e.desiredSide = !incoming) : False := by
  rcases S with ⟨hc,he,p,hp,a,ha,hx,hy,hb,hlenC,hlenE,hab⟩
  rw [c.portCoordinates_end w hw hc pos face incoming hcd hcf p,
    e.portCoordinates_end w hw he other face.opposite (!incoming) hed hef a] at hx hy
  have hbandA := Line.program_end_wall_band w (segmentLength e.segment) (e.above != e.desiredSide) e.above a ha
    (by cases incoming <;> simp only [Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false] at hx <;> omega)
  have hband : Line.StockBand w (Line.exitSide c.above (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) p.2.val := by
    have hcside : Line.exitSide c.above (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) = incoming := (c.exitSide_eq w).trans hcs
    have heside : Line.exitSide e.above (Line.program w (segmentLength e.segment) (e.above != e.desiredSide)) = !incoming := (e.exitSide_eq w).trans hes
    rw [hcside]
    rw [heside] at hbandA
    cases incoming <;> dsimp [Line.StockBand] at hbandA ⊢ <;> unfold FiniteTools.radius at * <;> omega
  exact Line.Action.last_not_stock w _ _ _ _ p hp (by
    cases incoming <;> simp only [Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false] at hx <;> omega) hband

private theorem end_start_impossible (S : SeamState w hw pos other face c e)
    (hcd : segmentDirection c.segment = face)
    (hcf : c.segment.finish = advance face.opposite (boundaryPoint w face) false.toNat)
    (hcs : c.desiredSide = false) (hed : segmentDirection e.segment = face.opposite.opposite)
    (hef : e.segment.start = boundaryPoint w face.opposite) (hea : e.above = false) : False := by
  rcases S with ⟨hc,he,p,hp,a,ha,hx,hy,hb,hlenC,hlenE,hab⟩
  rw [c.portCoordinates_end w hw hc pos face false hcd hcf p,
    e.portCoordinates_start w hw he other face.opposite hed hef a] at hx hy
  simp only [Bool.toNat_false] at hx
  have hbandA := Line.program_first_wall_band w (segmentLength e.segment) (e.above != e.desiredSide) e.above a ha
    (by unfold Line.buffer; omega)
  have hband : Line.StockBand w (Line.exitSide c.above (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) p.2.val := by
    have hcside : Line.exitSide c.above (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) = false := (c.exitSide_eq w).trans hcs
    rw [hcside]
    conv at hbandA => arg 2; rw [hea]
    dsimp [Line.StockBand] at hbandA ⊢
    omega
  exact Line.Action.last_not_stock w _ _ _ _ p hp (by
    omega) hband

private theorem start_end_impossible (S : SeamState w hw pos other face c e)
    (hcd : segmentDirection c.segment = face.opposite)
    (hcf : c.segment.start = boundaryPoint w face) (hca : c.above = false)
    (hed : segmentDirection e.segment = face.opposite)
    (hef : e.segment.finish = advance face.opposite.opposite (boundaryPoint w face.opposite) false.toNat)
    (hes : e.desiredSide = false) : False := by
  rcases S with ⟨hc,he,p,hp,a,ha,hx,hy,hb,hlenC,hlenE,hab⟩
  rw [c.portCoordinates_start w hw hc pos face hcd hcf p,
    e.portCoordinates_end w hw he other face.opposite false hed hef a] at hx hy
  simp only [Bool.toNat_false] at hx
  have hu := (Finset.mem_filter.mp hp).2
  have hpx : FiniteTools.radius w ≤ p.1.val := by
    change Line.Action.UsedPoint w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last p at hu
    rcases hu with hu | hu | hu <;> omega
  have hbandA := Line.program_last_wall_band w (segmentLength e.segment) (e.above != e.desiredSide) e.above a ha
    (by omega)
  have hband : Line.StockBand w c.above p.2.val := by
    have heside : Line.exitSide e.above (Line.program w (segmentLength e.segment) (e.above != e.desiredSide)) = false := (e.exitSide_eq w).trans hes
    conv => arg 2; rw [hca]
    rw [heside] at hbandA
    dsimp [Line.StockBand] at hbandA ⊢
    omega
  exact Line.Action.first_not_stock w _ _ _ _ p hp (by unfold Line.buffer; omega) hband

/-- Complementary real source ports leave the entire strict line action footprint free of neighboring walls. -/
theorem port_action_ne_wall (w : ℕ) (hw : 2 ≤ w) (pos other : ℕ × ℕ) (face : Direction)
    (hn : neighbor face pos = some other) (incoming : Bool) (c e : LineCode)
    (hc : LineGood w c.segment) (he : LineGood w e.segment)
    (hpc : LinePort w c face incoming) (hpe : LinePort w e face.opposite (!incoming))
    (p : c.ActionCell w)
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last)
    (q : Cell ((PrimitiveCode.line e).instanceOf w hw).width ((PrimitiveCode.line e).instanceOf w hw).height)
    (hq : q ∈ ((PrimitiveCode.line e).instanceOf w hw).board.walls) :
    macroShift w pos (c.actionWorld w hw p) ≠ macroShift w other ((PrimitiveCode.line e).world w hw q) := by
  obtain ⟨a,ha,heq⟩ := e.wall_world w hw q hq
  intro hh
  rw [heq] at hh
  have hxy := portCoordinates_neighbor w pos other (macroShift w pos (c.actionWorld w hw p)) face hn
  let S : SeamState w hw pos other face c e :=
    ⟨hc,he,p,hp,a,ha,(by rw [←hh]; exact hxy.1),(by rw [←hh]; exact hxy.2),
      (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2,
      Line.program_span_of_bound w _ _ hc.2.1,Line.program_span_of_bound w _ _ he.2.1,
      Line.walls_bounds w _ e.above ha⟩
  rcases hpc with ⟨hcd,hcf,_,hcs⟩ | ⟨hci,hcd,hcf,hca⟩
  · rcases hpe with ⟨hed,hef,_,hes⟩ | ⟨hei,hed,hef,hea⟩
    · exact end_end_impossible S incoming hcd hcf hcs hed hef hes
    · have hi : incoming = false := by cases incoming <;> simp_all
      exact end_start_impossible S hcd (by simpa only [hi] using hcf) (hcs.trans hi) hed hef hea
  · subst incoming
    rcases hpe with ⟨hed,hef,_,hes⟩ | ⟨hei,_,_,_⟩
    · exact start_end_impossible S hcd hcf hca hed hef hes
    · simp at hei

end PushPuzzle.PushS.FiniteRouting
