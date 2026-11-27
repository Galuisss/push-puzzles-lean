/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingDeepStock

/-! Interior working-row vacancies survive every foreign normal primitive. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem gate_deep_row_actor_ne (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : LineCode)
    (hc : .line c ∈ gateCodes w g) (hg : LineGood w c.segment)
    (n : ℕ) (hn : 3 ≤ n) (hn' : n+2 ≤ segmentLength c.segment)
    (hown : ∀ goal l, Line.along w (segmentDirection c.segment) c.segment.start n ≠
      (PrimitiveCode.line c).actor w hw goal l)
    (d : PrimitiveCode) (hd : d ∈ gateCodes w g) (goal : Bool) (l : d.Labels w) :
    Line.along w (segmentDirection c.segment) c.segment.start n ≠ d.actor w hw goal l := by
  obtain ⟨role,i,hi,rfl⟩ := gate_line_origin w g c hc
  let P := armSpec w g role
  have G : P.Geometry w := armSpec_geometry w g role
  have hp := (P.line i).deep_row_nearTrace w hw hg n (Nat.le_trans (Nat.le_add_right n 2) hn')
  have ha := (P.line i).deep_row_band w hg n hn hn'
  obtain ⟨u,hu,hu'⟩ := P.side_at w G i hi hp
  rw [gateCodes_eq_specs] at hd
  rcases List.mem_cons.mp hd with rfl | hd
  · by_cases hz : i = 0
    · subst i
      rw [armSpec_first_direction,armSpec_first_start]
      have hb := Bool.toNat_le (portInflow (coreSignals g goal).left (coreSignals g goal).upper
        (coreSignals g goal).right role)
      have hsep := core_ray_actor_separated w hw g role goal n (by omega) l
      intro he
      apply hsep
      rw [he]
      unfold Nearby
      omega
    · exact core_tail_actor_ne w hw g role (w+2) (by unfold FiniteGeometry.origin; omega)
        ⟨_,P.segment_mem_tail i hi (by omega),hu⟩ hu' goal l
  · obtain ⟨other,_,hd⟩ := List.mem_flatMap.mp hd
    by_cases he : role = other
    · subst other
      exact P.deep_ne_codes_actor w hw G i hi _ hp ha hown d hd goal l
    · obtain ⟨v,hv,hv'⟩ := (armSpec w g other).code_actor_trace w hw (armSpec_geometry w g other) d hd goal l
      apply footprint_ne (w := w) (m := w+2) (n := 2) _ hu' hv'
      intro hnear
      exact armRoutes_separated_wide w g he ⟨_,P.segment_mem i hi,hu⟩ hv (nearby_of_le (by omega) hnear)

theorem local_deep_row_actor_ne (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : LineCode)
    (hc : .line c ∈ FiniteSourceInventory.localCodes w code) (hg : LineGood w c.segment)
    (n : ℕ) (hn : 3 ≤ n) (hn' : n+2 ≤ segmentLength c.segment)
    (hown : ∀ goal l, Line.along w (segmentDirection c.segment) c.segment.start n ≠
      (PrimitiveCode.line c).actor w hw goal l)
    (d : PrimitiveCode) (hd : d ∈ FiniteSourceInventory.localCodes w code) (goal : Bool) (l : d.Labels w) :
    Line.along w (segmentDirection c.segment) c.segment.start n ≠ d.actor w hw goal l := by
  exact localCodes_pair_elim hc hd
    (fun g hcg hdg => gate_deep_row_actor_ne w hw g.2 c hcg hg n hn hn' hown d hdg goal l)
    (fun q hcq hdq => by
      obtain ⟨i,hi,rfl⟩ := (wireSpec w q.2).line_code_origin c hcq
      exact (wireSpec w q.2).deep_ne_codes_actor w hw (wireSpec_geometry w q.2) i hi _
        (((wireSpec w q.2).line i).deep_row_nearTrace w hw hg n (Nat.le_trans (Nat.le_add_right n 2) hn'))
        (((wireSpec w q.2).line i).deep_row_band w hg n hn hn') hown d hdq goal l)

end PushPuzzle.PushS.FiniteRouting
