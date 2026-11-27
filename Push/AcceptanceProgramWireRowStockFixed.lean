/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramWireRowStockRTrim
public import PushS.PortEndpointReaderWalk
import all Push.AcceptanceProgramWireRowStockGeometry
import all Push.AcceptanceProgramWireRowStockPaid
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramGuardStockReads
import all Push.AcceptanceSoundnessSupportCoordinatesGuards
import all PushS.PortEndpointLocality
import all PushS.PortReaderMidpoints
import all PushS.PortEndpointReaderWalk
import all PushS.EndpointWalking
import all PushS.PortWireGeometry
import all PushS.PortCoreCrossing
import all PushS.PortSegments
import all PushS.PortStreetSeparation
import all PushS.Scales

/-! The fixed R23 work-row stock is genuine earlier short-reader branches of deeper endpoints. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe

private theorem wireWorkRow_street (p : Scales.Parameters) (side : Side) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j ≤ p.levels) : wireWorkRow p side j ∈ streetRowCoordinates p := by
  change wireWorkRow p side j ∈ [0, p.H] ++ _
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨j - 1, List.mem_range.mpr (show j - 1 < (coordinates p).levels from by change j - 1 < p.levels; omega), ?_⟩
  have hj' : j - 1 + 1 = j := by omega
  rw [hj']
  change wireWorkRow p side j ∈ [readDepth p j, readDepth p j + 2, p.H - readDepth p j, p.H - (readDepth p j + 2)]
  rw [readDepth_eq p hj hjm]
  cases side <;> simp [wireWorkRow]

private theorem fixed_work_source (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.fixedSegments p))
    (hf : q ∉ Boundary.frame) (hn : q.2.val + 4 < p.D ∨ p.D + 4 < q.2.val) :
    q ∈ l.wideSeparatorHoles p ∨
      (∃ e ∈ l.endpoints, (q.1.val, q.2.val) ∈ pointHoles (endpointFixedSegments l (coordinates p) e)) ∨
      ∃ i ∈ l.gateCenterCoordinates, (q.1.val, q.2.val) ∈ pointHoles (gateFixedSegments (coordinates p) i) := by
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  rcases List.mem_append.mp hs with hs | hs
  · exact (hf (frame_contains (coordinates p) q ⟨s, hs, hc⟩)).elim
  dsimp only [markedInterior] at hs
  simp only [List.mem_append, or_assoc] at hs
  rcases hs with hs | hs | hs | hs
  · rw [roundedInterior_eq l p] at hs
    obtain ⟨old, hold, h_eq⟩ := List.mem_map.mp hs
    subst s
    simp only [interiorFixed, List.mem_append, or_assoc] at hold
    rcases hold with hs | hs | hs | hs | hs
    · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
      rw [rounded_endpoint l p hl hM e he hs] at hc
      exact Or.inr (Or.inl ⟨e, he, (mem_pointHoles _ _).mpr ⟨old, hs, hc⟩⟩)
    · obtain ⟨i, hi, hs⟩ := List.mem_flatMap.mp hs
      rw [rounded_gate l p i hs] at hc
      exact Or.inr (Or.inr ⟨i, hi, (mem_pointHoles _ _).mpr ⟨old, hs, hc⟩⟩)
    · exact Or.inl ((SegmentRecipe.mem_holes _ q).mpr ⟨_, List.mem_append_left _ (rounded_wide_mem l p .upper hs), hc⟩)
    · exact Or.inl ((SegmentRecipe.mem_holes _ q).mpr ⟨_, List.mem_append_right _ (rounded_wide_mem l p .lower hs), hc⟩)
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
      change (roundedPiece l p (point x p.D)).Contains (q.1.val, q.2.val) at hc
      rw [rounded_auxiliary l p hx] at hc
      have h := (point_coordinates hc).2
      dsimp only [coordinates] at h
      rcases hn with hn | hn <;> omega
  · obtain ⟨_, _, hs⟩ := List.mem_flatMap.mp hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    all_goals have h := (point_coordinates hc).2
    all_goals dsimp only [coordinates] at h
    all_goals rcases hn with hn | hn <;> omega
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hs
    have h := (point_coordinates hc).2
    change q.2.val = p.D - 4 at h
    rcases hn with hn | hn <;> omega
  · obtain ⟨_, _, hs⟩ := List.mem_flatMap.mp hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    all_goals have h := (point_coordinates hc).2
    all_goals change q.2.val = p.D + 4 at h
    all_goals rcases hn with hn | hn <;> omega

private theorem endpoint_midpoint_guard (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hrow : q.2.val ∈ streetRowCoordinates p)
    (hx : q.1.val = (EndpointStreet.f.column p e + p.x e.port) / 2)
    (hm : point q.1.val q.2.val ∈ endpointFixedSegments l (coordinates p) e) :
    q.1.val ∈ guards l p := by
  have hK : 14 ≤ p.K e.level := by have h := p.Q_ge; unfold Scales.Parameters.K; omega
  have hfar (x : ℕ) (hxs : x ∈ streetColumns l (coordinates p)) : 14 < Nat.dist q.1.val x := by
    have h := street_column_midpoint_far l p hl hM haxes he hxs
    rw [← hx, Nat.dist_comm] at h
    omega
  apply List.mem_toFinset.mpr
  apply (guard_mem_iff l (coordinates p) (l.fixedSegments p) q.1.val).mpr
  refine ⟨point q.1.val q.2.val, l.endpointFixedSegments_mem_fixed p hl hM e he hm, ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · simp only [point, PortLayout.segment, min_self, Bool.not_eq_true', Bool.eq_false_iff]
      intro hs
      have h := hfar q.1.val (List.contains_iff_mem.mp hs)
      rw [Nat.dist_self] at h
      omega
    · simpa only [point, PortLayout.segment, min_self] using List.contains_iff_mem.mpr (show q.2.val ∈ streetRows (coordinates p) from hrow)
    · apply List.all_eq_true.mpr
      intro x hx
      simpa only [point, PortLayout.segment, min_self] using decide_eq_true (hfar x hx)
  · simp only [point, PortLayout.segment, min_self]

private theorem work_row_ne_branch (p : Scales.Parameters) (side other : Side) {i j : ℕ}
    (hi : 1 ≤ i) (him : i ≤ p.levels) (hj : 1 ≤ j) (hjm : j ≤ p.levels)
    {y : ℕ} (hy : y = wireWorkRow p side j)
    (hb : y = onSide (coordinates p) other (p.Y i + 2)) : False := by
  have hiH := readDepth_add_lt_H p i
  rw [readDepth_eq p hi him] at hiH
  have hband : if other = .upper then p.Y i ≤ y ∧ y ≤ p.Y i + 2
      else p.H - (p.Y i + 2) ≤ y ∧ y ≤ p.H - p.Y i := by
    cases hs : other <;> simp only [hs, onSide, coordinates, ite_true, reduceCtorEq, ite_false] at hb ⊢ <;> omega
  obtain ⟨rfl, rfl⟩ := work_band_owner p side other hi him hj hjm hy hband
  cases other <;> simp only [wireWorkRow, onSide, coordinates, ite_true, reduceCtorEq, ite_false] at hy hb <;> omega

private theorem wireWork_guard_excluded (l : PortLayout) (p : Scales.Parameters) {q : Cell (p.W + 1) (p.H + 1)}
    {E : Finset (Cell (p.W + 1) (p.H + 1))}
    (hq : q ∈ (emit (wireWorkPrefix l p []) E).remaining) : q.1.val ∉ guards l p := by
  have hs : readColumns p .south (guards l p) ∈ wireWorkPrefix l p [] := by
    simp [wireWorkPrefix, schedule, preparation, frameSchedule]
  exact fun hx => emit_stage_excluded hs hq ((readColumns_region p .south _ (Or.inr rfl) q).mpr hx)

private theorem endpoint_fixed_work_short (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (side : Side) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels)
    {E : Finset (Cell (p.W + 1) (p.H + 1))} {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (emit (wireWorkPrefix l p []) E).remaining)
    (hy : q.2.val = wireWorkRow p side j)
    (e : Endpoint) (he : e ∈ l.endpoints)
    (hf : (q.1.val, q.2.val) ∈ pointHoles (endpointFixedSegments l (coordinates p) e)) :
    q ∈ l.endpointShortBranches p e := by
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp hf
  have hsAll := hs
  by_cases hs2 : s ∈ (endpointFixedSegments l (coordinates p) e).take 2
  · have htrim := endpoint_corridors_trim l p hl hM e he ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs2, hc⟩)
    exact (emit_stage_excluded (trimRound_mem_wireWorkPrefix l p [] e.side) hq htrim).elim
  obtain ⟨he0, heM⟩ := l.endpoints_level_bounds p hl hM he
  have hcX : (coordinates p).x = p.x := rfl
  have hcY : (coordinates p).depth e.level = p.Y e.level := readDepth_eq p he0 heM
  have hcH : (coordinates p).H = p.H := rfl
  dsimp only [endpointFixedSegments] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hs
  rcases hs with rfl | rfl | rfl | hs | hs
  · exact (hs2 (by simp [endpointFixedSegments])).elim
  · exact (hs2 (by simp [endpointFixedSegments])).elim
  · have hb := (horizontal_coordinates hc).1
    rw [hcY] at hb
    exact (work_row_ne_branch p side e.side he0 heM hj hjm hy hb).elim
  · obtain ⟨v, hv, hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_append.mp hs with hs | hs
    · split at hs
      next hvy =>
        simp only [List.mem_singleton] at hs
        subst s
        have hp := point_coordinates hc
        dsimp only [Prod.fst, Prod.snd] at hp
        have hx : q.1.val = (EndpointStreet.f.column p e + p.x e.port) / 2 := hp.1
        have hm : point q.1.val q.2.val ∈ endpointFixedSegments l (coordinates p) e := by
          rw [hp.1, hp.2]
          exact hsAll
        have hguard := endpoint_midpoint_guard l p hl hM haxes e he
          (hy ▸ wireWorkRow_street p side hj hjm) hx hm
        exact (wireWork_guard_excluded l p hq hguard).elim
      next hvy => cases hs
    · split at hs
      next hvy =>
        simp only [List.mem_singleton] at hs
        subst s
        have hp := point_coordinates hc
        dsimp only [Prod.fst, Prod.snd] at hp
        apply (mem_endpointShortBranches l p e q).mpr
        refine ⟨?_, v, hv, hvy, hp.2⟩
        change q.1.val = inward (p.x e.port) e.inward 1
        exact hp.1
      next hvy => cases hs
  · split at hs
    next hlev =>
      change e.level < p.levels at hlev
      have hcNext : (coordinates p).depth (e.level + 1) = p.Y (e.level + 1) := readDepth_eq p (by omega) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      all_goals
        have hr := (point_coordinates hc).2
        rw [hcY, hcNext] at hr
        have hr' : q.2.val = interlevelRow p e.side e.level := hr
        have hwork : q.2.val ∈ workRows l p := hy ▸ (level_work_rows l p side hj hjm).1
        exact (interlevelRow_not_work l p e.side he0 hlev (hr' ▸ hwork)).elim
    next hlev => cases hs

private theorem gate_fixed_work_impossible (l : PortLayout) (p : Scales.Parameters)
    (side : Side) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels) (hordinary : side = .upper ∨ 2 ≤ j)
    {E : Finset (Cell (p.W + 1) (p.H + 1))} {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (emit (wireWorkPrefix l p []) E).remaining)
    (hy : q.2.val = wireWorkRow p side j)
    {i : ℕ} (hi : i ∈ l.gateCenterCoordinates)
    (hf : (q.1.val, q.2.val) ∈ pointHoles (gateFixedSegments (coordinates p) i)) : False := by
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp hf
  by_cases hs4 : s ∈ (gateFixedSegments (coordinates p) i).take 4
  · exact emit_stage_excluded (trimRound_mem_wireWorkPrefix l p [] .lower) hq
      (gate_corridors_trim l p i hi ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs4, hc⟩))
  rw [← List.take_append_drop 4 (gateFixedSegments (coordinates p) i), List.mem_append] at hs
  rcases hs with hs | hs
  · exact hs4 hs
  have hcY : (coordinates p).depth 1 = p.Y 1 := readDepth_eq p le_rfl p.levels_pos
  have hcH : (coordinates p).H = p.H := rfl
  have hH := readDepth_add_lt_H p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hH
  have hwork : q.2.val ∈ workRows l p := hy ▸ (level_work_rows l p side hj hjm).1
  have hband (hb : p.H - (p.Y 1 + 2) ≤ q.2.val ∧ q.2.val ≤ p.H - p.Y 1) : False := by
    obtain ⟨hs, hj1⟩ := work_band_owner p side .lower le_rfl p.levels_pos hj hjm hy hb
    rcases hordinary with hu | hj2
    · rw [hu] at hs
      cases hs
    · omega
  dsimp only [gateFixedSegments] at hs
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.drop_succ_cons, List.drop_zero, List.mem_cons] at hs
  rcases hs with rfl | hbranch | rfl | rfl | hmarkers
  · have hp := (point_coordinates hc).2
    simp only [onSide, hcY, hcH, reduceCtorEq, ite_false] at hp
    apply hband
    omega
  · subst s
    have hp := (horizontal_coordinates hc).1
    simp only [onSide, hcY, hcH, reduceCtorEq, ite_false] at hp
    apply hband
    omega
  · have hp := (point_coordinates hc).2
    simp only [onSide, hcY, hcH, reduceCtorEq, ite_false] at hp
    exact halfRow_not_workRows l p (hp ▸ hwork)
  · have hp := (point_coordinates hc).2
    simp only [onSide, hcY, hcH, reduceCtorEq, ite_false] at hp
    exact halfRow_not_workRows l p (hp ▸ hwork)
  · split at hmarkers
    next hlevel =>
      obtain ⟨col, _, rfl⟩ := List.mem_map.mp hmarkers
      have hp := (point_coordinates hc).2
      have hlevel' : 1 < p.levels := hlevel
      have hcNext : (coordinates p).depth 2 = p.Y 2 := readDepth_eq p (by omega) (by omega)
      have hp' : q.2.val = interlevelRow p .lower 1 := by
        simpa only [onSide, hcY, hcNext, hcH, interlevelRow, interlevelDepth, reduceCtorEq, ite_false, Nat.reduceAdd] using hp
      exact interlevelRow_not_work l p .lower le_rfl hlevel' (hp' ▸ hwork)
    next hlevel => cases hmarkers

/-- Every actual fixed R23 hole on an ordinary work row is an existing short reader branch of a deeper endpoint on that page. -/
theorem wireRowFixedStock_short (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (hgate : l.gateCenterCoordinates ≠ []) (side : Side) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j ≤ p.levels) (hordinary : side = .upper ∨ 2 ≤ j)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ wireRowFixedStock l p side j) :
    ∃ e ∈ l.endpoints, e.side = side ∧ j < e.level ∧ q ∈ l.endpointShortBranches p e := by
  obtain ⟨hq, hy⟩ := Finset.mem_filter.mp hq
  have hf := emit_remaining_subset _ _ hq
  have hqref : q ∈ wireWorkReference l p [] := by
    rw [wireWorkReference, emit_remaining]
    obtain ⟨ht, hm⟩ := Finset.mem_sdiff.mp (by simpa only [emit_remaining] using hq)
    obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp ht
    exact Finset.mem_sdiff.mpr ⟨(SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_left _ hs, hc⟩, hm⟩
  have hframe := (Finset.mem_sdiff.mp (take_stock_interior l p [] 23 (by omega) hqref)).2
  have hD := readDepth_add_lt_D p j
  rw [readDepth_eq p hj hjm] at hD
  have hH : p.H = 2 * p.D := rfl
  have hcentral : q.2.val + 4 < p.D ∨ p.D + 4 < q.2.val := by
    cases side <;> simp only [wireWorkRow, ite_true, reduceCtorEq, ite_false] at hy <;> omega
  rcases fixed_work_source l p hl hM hf hframe hcentral with hwide | ⟨e, he, heq⟩ | ⟨i, hi, hiq⟩
  · exact (wireWork_guard_excluded l p hq (l.wideSeparatorHoles_guard_of_gate p hl hgate hwide)).elim
  · have hs := endpoint_fixed_work_short l p hl hM haxes side hj hjm hq hy e he heq
    have hpage := fixed_endpoint_page l p e heq
    have heside : e.side = side := by
      cases es : e.side <;> cases ss : side <;>
        simp only [es, ss, wireWorkRow, ite_true, reduceCtorEq, ite_false] at hpage hy ⊢ <;> omega
    obtain ⟨_, v, hv, hvlt, hvrow⟩ := (mem_endpointShortBranches l p e q).mp hs
    have hvH := workingRows_le_last l p hv
    have hlast := last_depth_margin p
    have hvj : v = p.Y j := by
      rw [heside] at hvrow
      cases side <;> simp only [wireWorkRow, ite_true, reduceCtorEq, ite_false] at hy hvrow <;> omega
    obtain ⟨he0, heM⟩ := l.endpoints_level_bounds p hl hM he
    have hlevel : j < e.level := by
      by_contra hn
      have hle := Y_le p (show e.level ≤ j by omega)
      rw [readDepth_eq p he0 heM, hvj] at hvlt
      omega
    exact ⟨e, he, heside, hlevel, hs⟩
  · exact (gate_fixed_work_impossible l p side hj hjm hordinary hq hy hi hiq).elim

end PushPuzzle.Push.AcceptanceProgram
