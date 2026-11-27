/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessGateProbeLocation
public import Push.AcceptanceProgramProbeStockSignals
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramWireRowStockFixed
import all PushS.PortReaderFreeze
import all PushS.PortPublicWalkBudget
import all PushS.PortEndpointReaderWalk
import all PushS.PortGatePageWindow
import all PushS.PortEndpointCrossing
import all PushS.PortCoreCrossing
import all PushS.PortSegments

/-! Every original non-main probe-row hole is a permanently empty fixed public, reader, midpoint or wide point. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- Every original non-main upper probe hole stays empty throughout the genuine accepted trajectory. -/
theorem canonical_upper_probe_source_empty
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ PushS.holes (I).initial)
    (hrow : q.2.val ∈ probeRows l p) (hnmain : q.1 ∉ l.mainColumnSet p) : q ∈ PushS.holes u := by
  have hraw : q ∈ targetHoles l p initial := by
    rw [← canonical_initial_holes l p hl hM haxes initial target]
    exact hq
  obtain ⟨ref, href, hy⟩ := List.mem_map.mp (List.mem_toFinset.mp hrow)
  obtain ⟨href, _⟩ := List.mem_filter.mp href
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM href
  change p.Y ref.level + 2 = q.2.val at hy
  have hY := readDepth_ge p hj hjm
  have hD := readDepth_add_lt_D p ref.level
  have hH : p.H = 2 * p.D := rfl
  rw [readDepth_eq p hj hjm] at hY hD
  have hwork : q.2.val ∈ workRows l p := hy ▸ (level_work_rows l p .upper hj hjm).2
  have hframe : q ∉ Boundary.frame := by
    intro hf
    obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
    cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd
    · omega
    · exact hnmain ((l.mainColumnSet_iff p q.1).mpr (Or.inr (Or.inl (by omega))))
    · omega
    · exact hnmain ((l.mainColumnSet_iff p q.1).mpr (Or.inl hd))
  have hfixed : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.fixedSegments p) := by
    obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hraw
    rcases List.mem_append.mp hs with hs | hs
    · exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hc⟩
    · have hsig := (signal_probe_rows l p hl hM haxes initial).mp
        ⟨(mem_pointHoles _ _).mpr ⟨s, hs, hc⟩, hrow⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hsig
      have hx := congrArg (fun q : Cell (p.W + 1) (p.H + 1) => q.1.val) hi
      change p.x i.val = q.1.val at hx
      exact (hnmain ((l.mainColumnSet_iff p q.1).mpr (Or.inr (Or.inr ⟨i.val, i.isLt, hx.symm⟩)))).elim
  rcases fixed_work_source l p hl hM hfixed hframe (Or.inl (by omega)) with hwide | ⟨e, he, hfixed⟩ | ⟨i, _, hfixed⟩
  · exact (canonical_wide_excluded_at l p hl hM haxes initial target hgate hsu hut ha).empty hwide
  · obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp hfixed
    by_cases hbase : s ∈ (endpointFixedSegments l (coordinates p) e).take 3
    · apply (canonical_publicWalkInvariant l p hl hM haxes initial target hgate ha) _ hsu hut
      exact Finset.mem_union_right _ ((SegmentRecipe.mem_holes _ q).mpr ⟨s, ordinary_public_mem l p he hbase, hc⟩)
    obtain ⟨he0, heM⟩ := l.endpoints_level_bounds p hl hM he
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
        have hread : (coordinates p).depth e.level = p.Y e.level := readDepth_eq p he0 heM
        have hnext : (coordinates p).depth (e.level + 1) = p.Y (e.level + 1) := readDepth_eq p (by omega) (by omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        all_goals
          have hyr := (point_coordinates hc).2
          rw [hread, hnext] at hyr
          have hycut : q.2.val = interlevelRow p e.side e.level := hyr
          exact (interlevelRow_not_work l p e.side he0 hlev (hycut ▸ hwork)).elim
      · cases hs
  · have hpage := gate_fixed_page p i hfixed
    omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
