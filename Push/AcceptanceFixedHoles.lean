/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateWalks
public import Push.AcceptanceSoundnessSupportCut
import all Push.AcceptanceProgramWireRowStockFixed
import all PushS.PortReaderFreeze
import all PushS.PortPublicWalkBudget
import all PushS.PortEndpointReaderWalk
import all PushS.PortGatePrivateWalk
import all PushS.PortGatePublicWalk
import all PushS.PortGateMarkers
import all PushS.PortGateHalfMarkers
import all PushS.PortSegments

/-! Every literal fixed hole remains empty throughout every actual accepted source trajectory. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

private theorem canonical_endpoint_fixed_holes_empty
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {e : Endpoint} (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : (q.1.val, q.2.val) ∈ pointHoles (endpointFixedSegments l (coordinates p) e)) :
    q ∈ PushS.holes u := by
  classical
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp hq
  by_cases hbase : s ∈ (endpointFixedSegments l (coordinates p) e).take 3
  · apply (canonical_publicWalkInvariant l p hl hM haxes initial target hgate ha) _ hsu hut
    exact Finset.mem_union_right _ ((SegmentRecipe.mem_holes _ q).mpr
      ⟨s, ordinary_public_mem l p he hbase, hc⟩)
  obtain ⟨he0, _⟩ := l.endpoints_level_bounds p hl hM he
  dsimp only [endpointFixedSegments] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hs
  rcases hs with rfl | rfl | rfl | hs | hs
  · exact (hbase (by simp [endpointFixedSegments])).elim
  · exact (hbase (by simp [endpointFixedSegments])).elim
  · exact (hbase (by simp [endpointFixedSegments])).elim
  · obtain ⟨v, hv, hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_append.mp hs with hs | hs
    · split at hs
      · rename_i hle
        simp only [List.mem_singleton] at hs
        subst s
        have hp := point_coordinates hc
        apply (canonical_allMidpointRows_excluded l p hl hM haxes initial target hgate e.level hsu hut ha).empty
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, e, he, rfl, hp.1, v, hv, hle, hp.2⟩
      · cases hs
    · split at hs
      · rename_i hlt
        simp only [List.mem_singleton] at hs
        subst s
        have hp := point_coordinates hc
        apply canonical_ordinaryReaders_empty l p hl hM haxes initial target hgate e he hsu hut ha
        apply Finset.mem_union_right
        apply Finset.mem_union_right
        exact (mem_endpointShortBranches l p e q).mpr ⟨hp.1, v, hv, hlt, hp.2⟩
      · cases hs
  · split at hs
    · rename_i hlev
      change e.level < p.levels at hlev
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · have hp := point_coordinates hc
        apply (canonical_allInterlevel_excluded l p hl hM haxes initial target hgate e.level he0 hsu hut ha).empty
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, rfl, hlev, .f, hp.1, hp.2⟩
      · have hp := point_coordinates hc
        apply (canonical_allInterlevel_excluded l p hl hM haxes initial target hgate e.level he0 hsu hut ha).empty
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, rfl, hlev, .r, hp.1, hp.2⟩
    · cases hs

private theorem canonical_gate_fixed_holes_empty
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : (q.1.val, q.2.val) ∈ pointHoles (gateFixedSegments (coordinates p) middle)) :
    q ∈ PushS.holes u := by
  classical
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp hq
  by_cases hbase : s ∈ (gateFixedSegments (coordinates p) middle).take 4
  · apply canonical_gate_publicWalk_empty l p hl hM haxes initial target hgate hi hsu hut ha
    exact gatePublicSegments_subset_walk p middle ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hbase, hc⟩)
  dsimp only [gateFixedSegments] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hs
  rcases hs with hs | rfl | rfl | rfl | rfl | hs
  · exact (hbase (by simpa only [gateFixedSegments, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero] using hs)).elim
  · apply canonical_gate_privateWalk_empty l p hl hM haxes initial target hgate hi hsu hut ha
    apply Finset.mem_union_right
    exact (SegmentRecipe.mem_holes _ q).mpr ⟨_, by
      rw [private_segments]
      exact List.mem_cons_self, hc⟩
  · apply canonical_gate_privateWalk_empty l p hl hM haxes initial target hgate hi hsu hut ha
    apply Finset.mem_union_right
    exact (SegmentRecipe.mem_holes _ q).mpr ⟨_, by
      rw [private_segments]
      exact List.mem_cons_of_mem _ List.mem_cons_self, hc⟩
  · have hp := point_coordinates hc
    apply (canonical_gate_halfMarkers_excluded l p hl hM haxes initial target hgate hsu hut ha).empty
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, middle, hi, Or.inl hp.1, hp.2⟩
  · have hp := point_coordinates hc
    apply (canonical_gate_halfMarkers_excluded l p hl hM haxes initial target hgate hsu hut ha).empty
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, middle, hi, Or.inr hp.1, hp.2⟩
  · split at hs
    · rename_i hlevels
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
      have hp := point_coordinates hc
      apply (canonical_gate_interlevel_excluded l p hl hM haxes initial target hgate hsu hut ha).empty
      have hxq : q.1.val = x := hp.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlevels, middle, hi, hxq ▸ hx, hp.2⟩
    · cases hs

/-- All actual fixed-segment holes stay empty at every prefix of the same accepted source play. -/
theorem canonical_allfixed_holes_empty
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.fixedSegments p) ⊆ PushS.holes u := by
  classical
  intro q hq
  by_cases hf : q ∈ Boundary.frame
  · exact (PushS.mem_holes _).mpr fun hb =>
      Finset.disjoint_left.mp (canonical_frame_empty_at l p hl hM haxes initial target hut ha) hb hf
  by_cases hc : q ∈ l.centralMarkers p
  · exact (canonical_central_markers_excluded_at l p hl hM haxes initial target hsu hut ha).empty hc
  have hoff : q.2.val + 4 < p.D ∨ p.D + 4 < q.2.val := by
    by_contra hn
    apply hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hq, hf⟩, by omega⟩
  rcases fixed_work_source l p hl hM hq hf hoff with hw | ⟨e, he, heq⟩ | ⟨middle, hi, hiq⟩
  · exact (canonical_wide_excluded_at l p hl hM haxes initial target hgate hsu hut ha).empty hw
  · exact canonical_endpoint_fixed_holes_empty l p hl hM haxes initial target hgate hsu hut ha he heq
  · exact canonical_gate_fixed_holes_empty l p hl hM haxes initial target hgate hsu hut ha hi hiq

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
