/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointLevelFWalk
public import PushS.PortEndpointLevelRWall

/-! Actual public long branches at every descending level. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

private noncomputable def publicSeparator (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) : EndpointWideSeparator l p e (readDepth p e.level + 2) :=
  Classical.choice (l.endpointWideSeparator_after_nonempty p hl hM ha he)

/-- The computed r-column tail and inward wall protecting an endpoint's public long branch. -/
noncomputable def endpointPublicBlockers (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  ((l.pageFrozenBlockers p hl ∪ l.interlevelMarkers p e.level) ∪ endpointTail p e .r) ∪
    l.levelRWall p e (publicSeparator l p hl hM ha e he)

/-- The actual protected r tail anchors the entire inward wall used by the public branch. -/
theorem endpointPublicBlockers_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level < p.levels) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial
      (l.pageBlockers p hl ∪ l.interlevelMarkers p e.level) (l.endpointPublicBlockers p hl hM ha e he) := by
  apply Freeze.Closure.add (l.endpointTail_closure p hl hM ha initial target e he heM .r)
    (l.levelRWall_initial_full p hl hM ha initial target e he _)
  apply l.levelRWall_anchored p hl hM e he _ _
    (fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h))
  intro q hx hy
  exact Finset.mem_union_right _ (l.endpointTail_start_mem p hl hM e he heM .r hx hy)

/-- The computed inward wall supplies every public-branch boundary guard. -/
theorem endpointPublicBlockers_emptyBoundary (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) :
    Freeze.EmptyBoundary (endpointPublicWalk p e) (endpointFWalk p e)
      (l.endpointPublicBlockers p hl hM ha e he) := by
  apply l.endpointPublicWalk_emptyBoundary_of_back p hl ha e he _
    (fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
  intro b hx hy
  have hb := l.levelRWall_branch_back_mem p hl e (publicSeparator l p hl hM ha e he) hx hy
  rcases Finset.mem_union.mp hb with hp | hw
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hp))
  · exact Finset.mem_union_right _ hw

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
  (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level < p.levels)

include he heM

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- Clearing deeper public walks certifies this level's f corridor and entire long branch. -/
theorem physicalInstance_level_publicWalk_empty {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals)
    (hP : ∀ s, Reachable (I).board none (I).initial s → Reachable (I).board none s t →
      l.deeperWalkHoles p e.level ⊆ holes s) : endpointPublicWalk p e ⊆ holes u := by
  have hguard := (l.endpointPublicBlockers_closure p hl hM ha initial target e he heM).reachable
    (l.physicalInstance_interlevel_avoiding_prefix p hl hM ha initial target e.level
      (l.endpoints_level_bounds p hl hM he).1 hsu hut ht hP)
  exact l.physicalInstance_endpoint_publicWalk_empty_of_avoiding p hl hM ha initial target e he
    (l.endpointPublicBlockers p hl hM ha e he) (l.endpointPublicBlockers_emptyBoundary p hl hM ha e he)
    hguard hut (fun _ hs ht' => l.physicalInstance_level_fwalk_empty p hl hM ha initial target e he heM hs ht' ht hP)

end Solution

/-- At any descending level the actual reader region is empty once all deeper public walks are empty. -/
theorem physicalInstance_level_readerWalk_empty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (j : ℕ) (hjM : j < p.levels) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals)
    (hP : ∀ s, Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial s →
      Reachable (l.physicalInstance p hl hM ha initial target).board none s t →
      l.deeperWalkHoles p j ⊆ holes s) : l.readerWalkHoles p j ⊆ holes u := by
  apply l.readerWalkHoles_subset_of_deeper_public p hl hM j (holes u) (hP u hsu hut)
  intro e he hej
  apply l.physicalInstance_level_publicWalk_empty p hl hM ha initial target e he (by omega) hsu hut ht
  simpa only [hej] using hP

end PushPuzzle.PushS.PortLayout
