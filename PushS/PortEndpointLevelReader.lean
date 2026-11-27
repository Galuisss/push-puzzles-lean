/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointLevelRWall
public import PushS.PortEndpointTail
public import PushS.PortEndpointReaderWalk
public import PushS.PortEndpointInnerWalls
import all PushS.PortEndpointInnerWalls
import all PushS.PortEndpointReaderWalk
import all PushS.PortBackground
import all PushS.EndpointMacros

/-! Actual r-reader closures on the descending levels. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

private noncomputable def levelReaderSeparator (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) :
    EndpointWideSeparator l p e (readDepth p e.level + 2) :=
  Classical.choice (l.endpointWideSeparator_after_nonempty p hl hM ha he)

/-- The actual page, interlevel tail, work-row wall, inner rows and half rods of this reader. -/
noncomputable def endpointLevelReaderBlockers (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  (((((l.pageFrozenBlockers p hl ∪ l.interlevelMarkers p e.level) ∪ endpointTail p e .r) ∪
      l.readerMidpointRows p e.level) ∪ l.levelRWall p e (levelReaderSeparator l p hl hM ha e he)) ∪
      l.endpointInnerWalls p hl hM ha e he) ∪ l.endpointFrontRods p e

private theorem level_inner_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) :
    l.endpointInnerWalls p hl hM ha e he ⊆
      (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  intro q hq
  obtain ⟨v, _, hq⟩ := Finset.mem_biUnion.mp hq
  exact l.endpointInnerWall_initial_full_general p hl hM ha initial target e he _
    (inner_depth_data l p e v).1 hq

/-- Every region in the computed reader blockers is frozen from the actual marker basis. -/
theorem endpointLevelReaderBlockers_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level < p.levels) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial
      ((l.pageBlockers p hl ∪ l.interlevelMarkers p e.level) ∪ l.readerMidpointRows p e.level)
      (l.endpointLevelReaderBlockers p hl hM ha e he) := by
  let g := levelReaderSeparator l p hl hM ha e he
  let G : Finset (Cell (p.W + 1) (p.H + 1)) :=
    ((l.pageFrozenBlockers p hl ∪ l.interlevelMarkers p e.level) ∪ endpointTail p e .r) ∪
      l.readerMidpointRows p e.level
  have hbase : Freeze.Closure (w := p.W + 1) (h := p.H + 1)
      (l.physicalInstance p hl hM ha initial target).initial
      ((l.pageBlockers p hl ∪ l.interlevelMarkers p e.level) ∪ l.readerMidpointRows p e.level) G :=
    (l.endpointTail_closure p hl hM ha initial target e he heM .r).adjoin_blockers
      (l.readerMidpointRows p e.level)
  have hpage : l.pageFrozenBlockers p hl ⊆ G :=
    fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hwall := l.levelRWall_closure p hl hM ha initial target e he g G hbase hpage
    (fun _ hx hy => Finset.mem_union_left _ (Finset.mem_union_right _
      (l.endpointTail_start_mem p hl hM e he heM .r hx hy)))
  have hinner := Freeze.Closure.add hwall
    (level_inner_full l p hl hM ha initial target e he)
    ((l.endpointInnerWalls_anchored p hl hM ha e he).mono_blockers
      (fun _ h => Finset.mem_union_left _ (hpage h)))
  exact .add hinner (l.endpointFrontRods_initial_full p hl hM ha initial target e he)
    (l.endpointFrontRods_anchored p hl ha e he _
      (fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ (hpage h)))
      (fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h))))

private theorem level_reader_page (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints) :
    l.pageFrozenBlockers p hl ⊆ l.endpointLevelReaderBlockers p hl hM ha e he := by
  intro q hq
  simp only [endpointLevelReaderBlockers, Finset.mem_union]
  tauto

/-- The computed finite closure supplies the complete actual reader boundary at this level. -/
theorem endpointLevelReaderBlockers_guards (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) :
    EndpointReaderGuards l p hl e (l.endpointLevelReaderBlockers p hl hM ha e he) := by
  constructor
  · exact level_reader_page l p hl hM ha e he
  · intro q hq hf hy r hadj
    have hq' := (mem_endpointRWalk_iff p e q).mp hq
    have hdepth : (if e.side = .upper then q.2.val else p.H - q.2.val) < readDepth p e.level := by
      have hqy := q.2.isLt
      cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hq' ⊢ <;> omega
    have hg := l.endpointInnerWalls_guard p hl hM ha e he hq'.1 hy hf hdepth hadj
    rcases Finset.mem_union.mp hg with hi | hp
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
    · exact level_reader_page l p hl hM ha e he hp
  · intro q hx hy
    have hg := l.levelRWall_cap_mem p hl e (levelReaderSeparator l p hl hM ha e he) hx hy
    rcases Finset.mem_union.mp hg with hp | hr
    · exact level_reader_page l p hl hM ha e he hp
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hr))
  · intro v hv hlt q hx hy
    exact Finset.mem_union_right _
      (l.endpointFrontRods_back_mem p hl hM e he hv (Nat.le_of_lt hlt) hx hy)

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
  (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level < p.levels)

include he heM

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- Clearing the deeper public walks and this level's long reader walks forces the actual
r corridor and all selected short branches empty at every successful prefix. -/
theorem physicalInstance_level_reader_empty {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u)
    (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals)
    (hP : ∀ s, Reachable (I).board none (I).initial s → Reachable (I).board none s t →
      l.deeperWalkHoles p e.level ⊆ holes s)
    (hR : ∀ s, Reachable (I).board none (I).initial s → Reachable (I).board none s t →
      l.readerWalkHoles p e.level ⊆ holes s) : l.endpointReaderWalk p e ⊆ holes u := by
  apply l.physicalInstance_endpoint_reader_empty_of_avoiding p hl hM ha initial target e he
    (l.endpointLevelReaderBlockers p hl hM ha e he)
    (l.endpointLevelReaderBlockers_guards p hl hM ha e he) ?_ hut ht
  apply (l.endpointLevelReaderBlockers_closure p hl hM ha initial target e he heM).reachable
  apply enrich_path hsu
  intro a b hsa hm hbu
  have hbt := hbu.trans hut
  have hmidA := l.physicalInstance_reader_midpointRows_excluded_at p hl hM ha initial target e.level
    hsa ((Relation.ReflTransGen.single hm).trans hbt) ht hR
  have hmidB := l.physicalInstance_reader_midpointRows_excluded_at p hl hM ha initial target e.level
    (hsa.tail hm) hbt ht hR
  exact (l.physicalInstance_interlevel_step_avoiding p hl hM ha initial target e.level
    (l.endpoints_level_bounds p hl hM he).1 hsa hm hbt ht hP).union_excluded hmidA hmidB

end Solution
end PushPuzzle.PushS.PortLayout
