/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteCoreActiveFloor

/-! Prepared real arm stocks leave the entire selected-core region empty. -/

public section
namespace PushPuzzle.PushS.FiniteGateActiveRegion

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteCoreGuardCoverage

attribute [local irreducible] FiniteGeometry.side Line.width Line.height Line.program Line.span

private theorem first_line_actor_clear (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (selected : Fin 3)
    (a : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (ha : Region w g.core.isAND selected a)
    (role : Fin 3) (goal : Bool) (l : (PrimitiveCode.line ((armSpec w g role).line 0)).Labels w)
    (hselected : role = selected →
      (if goal then (armSpec w g role).target else (armSpec w g role).initial) = true) :
    coreWorld w a ≠ (PrimitiveCode.line ((armSpec w g role).line 0)).actor w hw goal l := by
  let P := armSpec w g role
  intro he
  let atoms := Line.program w (segmentLength (P.line 0).segment) ((P.line 0).above != (P.line 0).desiredSide)
  let q := if goal then P.target else P.initial
  change Line.OwnedLabel w atoms false (P.line 0).last at l
  have hactor := line_actor w hw (P.line 0) (P.line_good w (armSpec_geometry w g role) 0 (by change 0 < (armRoute w g role).length; rw [armRoute_length,route_length]; omega)) goal l
  change _ = Line.along w (segmentDirection (P.line 0).segment) (P.line 0).segment.start
    (Line.position w atoms q l.val) at hactor
  have hd := armSpec_first_direction w g role
  have hs := armSpec_first_start w g role
  change segmentDirection (P.line 0).segment = _ at hd
  change (P.line 0).segment.start = _ at hs
  rw [hd,hs] at hactor
  have hbound := envelope_ray_bound w g.core.isAND role (Line.position w atoms q l.val) a ha.1 (hactor.symm.trans he.symm)
  have hlower := Line.owned_position_after_first w (segmentLength (P.line 0).segment) hw
    ((P.line 0).above != (P.line 0).desiredSide) q (P.line 0).last l
  change q.toNat+2 ≤ Line.position w atoms q l.val at hlower
  have hn : role ≠ selected := by
    intro hr
    have hq : q = true := hselected hr
    rw [hq] at hlower
    change 3 ≤ Line.position w atoms true l.val at hlower
    have hp : Line.position w atoms q l.val = Line.position w atoms true l.val := congrArg (fun q => Line.position w atoms q l.val) hq
    omega
  have hpos : Line.position w atoms q l.val = 2 := by have := Bool.toNat_le q; omega
  apply ha.2 role hn
  exact he.trans (hactor.trans (congrArg (Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role)) hpos))

/-- An actual arm's normal stock avoids the selected region whenever the selected arm is physically high. -/
theorem core_arm_actor_clear (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (selected : Fin 3)
    (a : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (ha : Region w g.core.isAND selected a)
    (role : Fin 3) (c : PrimitiveCode) (hc : c ∈ (armSpec w g role).codes)
    (goal : Bool) (l : c.Labels w)
    (hselected : role = selected →
      (if goal then (armSpec w g role).target else (armSpec w g role).initial) = true) :
    coreWorld w a ≠ c.actor w hw goal l := by
  let P := armSpec w g role
  have G := armSpec_geometry w g role
  rcases arm_code_cases w g role c hc with ⟨i,hi',rfl⟩ | ⟨i,ht,rfl⟩
  · by_cases hz : i = 0
    · subst i
      exact first_line_actor_clear w hw g selected a ha role goal l hselected
    · obtain ⟨u,hu,hactor⟩ := P.line_actor_at w hw G i hi' goal l
      have hh := core_tail_ne w hw g role 1 (by unfold origin; omega)
        ⟨_,P.segment_mem_tail i hi' (by omega),hu⟩ hactor (coreCell w hw g a)
      simpa only [coreCell_world] using Ne.symm hh
  · have hactor := P.turn_actor_at w hw G i ht goal l
    rw [P.join_eq w G i ht.1] at hactor
    have hh := core_tail_ne w hw g role 2 (by unfold origin; omega)
      ⟨_,P.segment_mem_tail (i+1) ht.1 (by omega),P.start_contains w G (i+1) ht.1⟩ hactor (coreCell w hw g a)
    simpa only [coreCell_world] using Ne.symm hh

end PushPuzzle.PushS.FiniteGateActiveRegion
