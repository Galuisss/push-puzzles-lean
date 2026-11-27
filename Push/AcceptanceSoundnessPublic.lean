/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessFWalk
public import PushS.PortEndpointLevelPublic
import all PushS.PortEndpointBranch
import all PushS.PortDeeperBudget
import all PushS.PortSegments

/-! Actual ordinary long branches and the descending reader-public region remain empty. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushFS.Reduction PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

include hgate

/-- The highest ordinary endpoint's entire public long branch remains empty along actual accepted play. -/
theorem canonical_last_publicWalk_empty (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level = p.levels) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    endpointPublicWalk p e ⊆ PushS.holes u := by
  obtain ⟨g⟩ := l.endpointWideSeparator_nonempty p hl haxes he
  have hguard := (l.endpointRWall_closure p hl hM haxes (l.canonical initial) (l.canonical target)
    e he g heM).reachable (canonical_page_avoiding_prefix l p hl hM haxes initial target hgate hsu hut ha)
  exact l.physicalInstance_endpoint_publicWalk_empty_of_avoiding p hl hM haxes
    (l.canonical initial) (l.canonical target) e he _
    (l.endpointPublicWalk_emptyBoundary p hl haxes e he g heM) hguard hut
    (fun _ hs ht => canonical_last_fwalk_empty_at l p hl hM haxes initial target hgate e he heM hs ht ha)

/-- The current ordinary endpoint's public long branch stays empty under the deeper-walk invariant. -/
theorem canonical_level_publicWalk_empty_of_deeper (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level < p.levels) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (hP : DeeperWalkInvariant l p hl hM haxes initial target e.level t) : endpointPublicWalk p e ⊆ PushS.holes u := by
  have hguard := (l.endpointPublicBlockers_closure p hl hM haxes (l.canonical initial) (l.canonical target)
    e he heM).reachable (canonical_interlevel_page_avoiding_prefix_of_deeper l p hl hM haxes initial target hgate
      e.level (l.endpoints_level_bounds p hl hM he).1 hsu hut ha hP)
  exact l.physicalInstance_endpoint_publicWalk_empty_of_avoiding p hl hM haxes
    (l.canonical initial) (l.canonical target) e he _
    (l.endpointPublicBlockers_emptyBoundary p hl hM haxes e he) hguard hut
    (fun _ hs ht => canonical_level_fwalk_empty_at_of_deeper l p hl hM haxes initial target hgate e he heM hs ht ha hP)

/-- At the highest cutoff the literal reader-public region consists entirely of empty frame and public walks. -/
theorem canonical_readerWalk_last_empty {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    l.readerWalkHoles p p.levels ⊆ PushS.holes u := by
  intro q hq
  rcases Finset.mem_union.mp hq with hf | hw
  · exact (PushS.mem_holes _).mpr fun hb =>
      Finset.disjoint_left.mp (canonical_frame_empty_at l p hl hM haxes initial target hut ha) hb hf
  · obtain ⟨s, hs, hcontains⟩ := (SegmentRecipe.mem_holes _ q).mp hw
    obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨⟨z, k⟩, hk, hs⟩ := List.mem_filterMap.mp hs
    dsimp only at hs
    have hsel : if k = 1 then p.levels < e.level else p.levels ≤ e.level := by
      by_contra h
      rw [ite_eq_right h] at hs
      cases hs
    rw [ite_eq_left hsel] at hs
    have heq : z = s := Option.some.inj hs
    subst z
    obtain ⟨heM, hpublic⟩ := last_reader_piece l p hl hM he hk hsel hcontains
    exact canonical_last_publicWalk_empty l p hl hM haxes initial target hgate e he heM hsu hut ha hpublic

/-- At every lower cutoff, the actual deeper-walk invariant and true public branches empty the reader-public region. -/
theorem canonical_level_readerWalk_empty_of_deeper (j : ℕ) (hjM : j < p.levels)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (hP : DeeperWalkInvariant l p hl hM haxes initial target j t) : l.readerWalkHoles p j ⊆ PushS.holes u := by
  apply l.readerWalkHoles_subset_of_deeper_public p hl hM j (PushS.holes u) (hP u hsu hut)
  intro e he hej
  apply canonical_level_publicWalk_empty_of_deeper l p hl hM haxes initial target hgate e he (by omega) hsu hut ha
  simpa only [hej] using hP

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
