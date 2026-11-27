/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessOrdinaryWalksMidpoints
public import PushS.PortEndpointLevelReader
import all Push.AcceptanceSoundnessCentral
import all PushS.PortBackground

/-! Actual midpoint protection closes the highest and descending ordinary r-reader regions. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

private theorem canonical_reader_empty_of_avoiding (e : Endpoint) (he : e ∈ l.endpoints)
    (G : Finset (Cell (p.W + 1) (p.H + 1))) (hg : EndpointReaderGuards l p hl e G)
    {u t : State (p.W + 1) (p.H + 1)}
    (hguard : Relation.ReflTransGen (Freeze.AvoidingStep
      (l.canonicalInstance p hl hM haxes initial target).board none G)
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    l.endpointReaderWalk p e ⊆ PushS.holes u := by
  apply (l.endpointReaderWalk_emptyBoundary p hl e he hg).reachable_holes
  · apply enrich_path hguard
    intro a b _ hm hbu
    have hbt : Reachable (l.canonicalInstance p hl hM haxes initial target).board none b t :=
      (Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ hbu).trans hut
    refine ⟨hm, ?_⟩
    intro q hq
    exact (PushS.mem_holes _).mpr fun hb =>
      Finset.disjoint_left.mp (canonical_frame_empty_at l p hl hM haxes initial target hbt ha) hb hq
  · intro q hq
    exact (congrArg (fun E : Finset (Cell (p.W + 1) (p.H + 1)) => q ∈ E)
      (canonical_initial_holes l p hl hM haxes initial target)).mpr
      (l.endpointReaderWalk_subset_encoded p hl hM haxes (l.canonical initial) e he hq)

variable (hgate : l.gateCenterCoordinates ≠ [])
include hgate

/-- The highest-level ordinary r corridor and all selected short branches stay empty on actual accepted prefixes. -/
theorem canonical_last_reader_empty (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level = p.levels) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    l.endpointReaderWalk p e ⊆ PushS.holes u := by
  have hR : ReaderWalkInvariant l p hl hM haxes initial target p.levels t :=
    fun _ hs ht => canonical_readerWalk_last_empty l p hl hM haxes initial target hgate hs ht ha
  apply canonical_reader_empty_of_avoiding l p hl hM haxes initial target e he _
    (l.endpointReaderBlockers_guards p hl hM haxes e he heM) ?_ hut ha
  apply (l.endpointReaderBlockers_closure p hl hM haxes (l.canonical initial) (l.canonical target) e he heM).reachable
  apply enrich_path hsu
  intro a b hsa hm hbu
  have hbt := hbu.trans hut
  exact (canonical_page_step_avoiding l p hl hM haxes initial target hgate hsa hm hbt ha).union_excluded
    (canonical_reader_midpointRows_excluded_at_of_reader l p hl hM haxes initial target p.levels
      hsa ((Relation.ReflTransGen.single hm).trans hbt) ha hR)
    (canonical_reader_midpointRows_excluded_at_of_reader l p hl hM haxes initial target p.levels
      (hsa.tail hm) hbt ha hR)

/-- The deeper-walk induction invariant closes the current ordinary r corridor and every short branch. -/
theorem canonical_level_reader_empty_of_deeper (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level < p.levels) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (hP : DeeperWalkInvariant l p hl hM haxes initial target e.level t) :
    l.endpointReaderWalk p e ⊆ PushS.holes u := by
  have hR : ReaderWalkInvariant l p hl hM haxes initial target e.level t :=
    fun _ hs ht => canonical_level_readerWalk_empty_of_deeper l p hl hM haxes initial target hgate
      e.level heM hs ht ha hP
  apply canonical_reader_empty_of_avoiding l p hl hM haxes initial target e he _
    (l.endpointLevelReaderBlockers_guards p hl hM haxes e he) ?_ hut ha
  apply (l.endpointLevelReaderBlockers_closure p hl hM haxes (l.canonical initial) (l.canonical target) e he heM).reachable
  apply enrich_path hsu
  intro a b hsa hm hbu
  have hbt := hbu.trans hut
  exact (canonical_interlevel_page_step_avoiding_of_deeper l p hl hM haxes initial target hgate e.level
    (l.endpoints_level_bounds p hl hM he).1 hsa hm hbt ha hP).union_excluded
    (canonical_reader_midpointRows_excluded_at_of_reader l p hl hM haxes initial target e.level
      hsa ((Relation.ReflTransGen.single hm).trans hbt) ha hR)
    (canonical_reader_midpointRows_excluded_at_of_reader l p hl hM haxes initial target e.level
      (hsa.tail hm) hbt ha hR)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
