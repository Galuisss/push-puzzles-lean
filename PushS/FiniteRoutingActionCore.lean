/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionPath
public import PushS.FiniteCoreGuardCoverage

/-! The complete routed line action footprint avoids every actual core wall. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls Line.program Line.span FiniteTools.side FiniteGeometry.side

/-- Canonical cells of the literal emitted program of one line instruction. -/
abbrev LineCode.ActionCell (w : ℕ) (c : LineCode) :=
  Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w)

private theorem LineCode.actionWorld_eq_placement (w : ℕ) (hw : 2 ≤ w) (c : LineCode)
    (ht : Travels (segmentDirection c.segment) c.segment.start c.segment.finish
      (Line.span w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))))
    (hs : c.segment.start.1 ≤ tileStride w ∧ c.segment.start.2 ≤ tileStride w)
    (hf : c.segment.finish.1 ≤ tileStride w ∧ c.segment.finish.2 ≤ tileStride w) (p : c.ActionCell w) :
    c.actionWorld w hw p = coordinates ((Line.placement w
      (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) (segmentDirection c.segment)
      c.segment.start c.segment.finish ht hs hf).cells p) := rfl

private theorem first_arm_action_ne_core (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3)
    (p : ((armSpec w g role).line 0).ActionCell w)
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength ((armSpec w g role).line 0).segment)
      (((armSpec w g role).line 0).above != ((armSpec w g role).line 0).desiredSide))
      ((armSpec w g role).line 0).above ((armSpec w g role).line 0).last)
    (q : Cell (FiniteGeometry.side w) (FiniteGeometry.side w))
    (hq : q ∈ FiniteCoreGuardCoverage.walls w g.core.isAND) :
    ((armSpec w g role).line 0).actionWorld w hw p ≠ coreWorld w q := by
  let c := (armSpec w g role).line 0
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have hi : 0 < (armSpec w g role).segments.length := by
    change 0 < (armRoute w g role).length
    rw [armRoute_length,route_length]
    omega
  have hc := (armSpec w g role).line_good w (armSpec_geometry w g role) 0 hi
  have hlen : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  have ht0 : Travels (segmentDirection c.segment) c.segment.start c.segment.finish (Line.span w atoms) := by
    rw [hlen]
    exact segment_travels c.segment hc.1
  have ht : Travels (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) c.segment.finish (Line.span w atoms) := by
    simpa only [c,armSpec_first_direction,armSpec_first_start] using ht0
  have hs : (corePort w g.core.isAND role).1 ≤ tileStride w ∧ (corePort w g.core.isAND role).2 ≤ tileStride w := by
    simpa only [armSpec_first_start] using hc.2.2.1
  have hu := (Finset.mem_filter.mp hp).2
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hpx : FiniteTools.radius w ≤ p.1.val := by
    change Line.Action.UsedPoint w atoms c.above c.last p at hu
    rcases hu with hu | hu | hu <;> omega
  intro he
  apply hb.2.2.2.2
  have hplace := c.actionWorld_eq_placement w hw ht0 hc.2.2.1 hc.2.2.2 p
  have hplace' : c.actionWorld w hw p = coordinates ((Line.placement w atoms (PortAnnulus.innerDirection role)
      (corePort w g.core.isAND role) c.segment.finish ht hs hc.2.2.2).cells p) := by
    simpa only [c,armSpec_first_direction,armSpec_first_start] using hplace
  have hhit : coordinates ((Line.placement w atoms (PortAnnulus.innerDirection role)
      (corePort w g.core.isAND role) c.segment.finish ht hs hc.2.2.2).cells p) = coreWorld w q := hplace'.symm.trans he
  exact FiniteCoreGuardCoverage.initial_stock_covers_core_wall w (segmentLength c.segment) hw g.core.isAND
    (c.above != c.desiredSide) role c.segment.finish ht hs hc.2.2.2 p hpx q hq hhit

theorem arm_action_ne_core_wall (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3)
    (i : ℕ) (hi : i < (armSpec w g role).segments.length)
    (p : ((armSpec w g role).line i).ActionCell w)
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength ((armSpec w g role).line i).segment)
      (((armSpec w g role).line i).above != ((armSpec w g role).line i).desiredSide))
      ((armSpec w g role).line i).above ((armSpec w g role).line i).last)
    (q : Cell ((PrimitiveCode.core g).instanceOf w hw).width ((PrimitiveCode.core g).instanceOf w hw).height)
    (hq : q ∈ ((PrimitiveCode.core g).instanceOf w hw).board.walls) :
    ((armSpec w g role).line i).actionWorld w hw p ≠ (PrimitiveCode.core g).world w hw q := by
  by_cases hz : i = 0
  · subst i
    rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
    cases kind
    · exact first_arm_action_ne_core w hw _ role p hp q hq
    · exact first_arm_action_ne_core w hw _ role p hp q hq
  · obtain ⟨u,hu,ha⟩ := (armSpec w g role).action_at w hw (armSpec_geometry w g role) i hi p hp
    exact core_tail_ne w hw g role (w+2) (by unfold FiniteGeometry.origin; omega)
      ⟨_,(armSpec w g role).segment_mem_tail i hi (by omega),hu⟩ ha q

end PushPuzzle.PushS.FiniteRouting
