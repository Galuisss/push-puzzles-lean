/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointReaderWalk
public import PushS.PortEndpointInnerWalls
public import PushS.PortDeeperBudget
import all PushS.PortEndpointReaderWalk
import all PushS.PortDeeperBudget
import all PushS.PortEndpointFStock
import all PushS.PortEndpointBranch
import all PushS.EndpointMacros
import all PushS.PortSegments

/-! The concrete last-level reader closure combines the page, midpoint rods, and side walls. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

private noncomputable def lastReaderSeparator (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints) :
    EndpointWideSeparator l p e := Classical.choice (l.endpointWideSeparator_nonempty p hl ha he)

/-- The computed page, midpoint, half-rod, r-cap and inner-wall blockers of a last-level reader. -/
noncomputable def endpointReaderBlockers (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  (((l.pageFrozenBlockers p hl ∪ l.readerMidpointRows p p.levels) ∪ l.endpointFrontRods p e) ∪
    l.endpointRWall p e (lastReaderSeparator l p hl ha e he)) ∪
      l.endpointInnerWalls p hl hM ha e he

private theorem reader_page_subset (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints) :
    l.pageFrozenBlockers p hl ⊆ l.endpointReaderBlockers p hl hM ha e he := by
  intro q hq
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hq)))

/-- All components of the computed last-level reader blockers have actual freezing certificates. -/
theorem endpointReaderBlockers_closure (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level = p.levels) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial
      (l.pageBlockers p hl ∪ l.readerMidpointRows p p.levels)
      (l.endpointReaderBlockers p hl hM ha e he) := by
  have hbase : Freeze.Closure (w := p.W + 1) (h := p.H + 1)
      (l.physicalInstance p hl hM ha initial target).initial
      (l.pageBlockers p hl ∪ l.readerMidpointRows p p.levels)
      (l.pageFrozenBlockers p hl ∪ l.readerMidpointRows p p.levels) :=
    (l.pageBackground_closure p hl hM ha initial target).adjoin_blockers (l.readerMidpointRows p p.levels)
  have hfront := l.endpointFrontRods_anchored p hl ha e he
    (l.pageFrozenBlockers p hl ∪ l.readerMidpointRows p p.levels) Finset.subset_union_left
    (by rw [heM]; exact Finset.subset_union_right)
  have hfirst := Freeze.Closure.add hbase
    (l.endpointFrontRods_initial_full p hl hM ha initial target e he) hfront
  have hr : Freeze.Anchored (l.endpointRWall p e (lastReaderSeparator l p hl ha e he))
      ((l.pageFrozenBlockers p hl ∪ l.readerMidpointRows p p.levels) ∪ l.endpointFrontRods p e) :=
    (l.endpointRWall_anchored p hl hM ha e he (lastReaderSeparator l p hl ha e he) heM).mono_blockers
    (fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hsecond := Freeze.Closure.add hfirst
    (l.endpointRWall_initial_full p hl hM ha initial target e he (lastReaderSeparator l p hl ha e he) heM) hr
  have hi : Freeze.Anchored (l.endpointInnerWalls p hl hM ha e he)
      (((l.pageFrozenBlockers p hl ∪ l.readerMidpointRows p p.levels) ∪ l.endpointFrontRods p e) ∪
        l.endpointRWall p e (lastReaderSeparator l p hl ha e he)) :=
    (l.endpointInnerWalls_anchored p hl hM ha e he).mono_blockers
    (fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
  exact Freeze.Closure.add hsecond (l.endpointInnerWalls_initial_full p hl hM ha initial target e he heM) hi

/-- The actual finite reader closure supplies every guard required by its exact EmptyBoundary. -/
theorem endpointReaderBlockers_guards (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level = p.levels) : EndpointReaderGuards l p hl e (l.endpointReaderBlockers p hl hM ha e he) := by
  constructor
  · exact reader_page_subset l p hl hM ha e he
  · intro q hq hf hy r hadj
    have hq' := (mem_endpointRWalk_iff p e q).mp hq
    have hY := readDepth_add_lt_H p e.level
    have hdepth : (if e.side = .upper then q.2.val else p.H - q.2.val) < readDepth p e.level := by
      have hqy := q.2.isLt
      cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hq' ⊢ <;> omega
    have hg := l.endpointInnerWalls_guard p hl hM ha e he hq'.1 hy hf hdepth hadj
    rcases Finset.mem_union.mp hg with hi | hp
    · exact Finset.mem_union_right _ hi
    · exact reader_page_subset l p hl hM ha e he hp
  · intro q hx hy
    have hg := l.endpointRWall_cap_mem p hl e (lastReaderSeparator l p hl ha e he) heM hx hy
    rcases Finset.mem_union.mp hg with hp | hr
    · exact reader_page_subset l p hl hM ha e he hp
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hr)
  · intro v hv hlt q hx hy
    have hg := l.endpointFrontRods_back_mem p hl hM e he hv (Nat.le_of_lt hlt) hx hy
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hg))

/-- The actual r corridor and every selected short branch stay empty on every successful play. -/
theorem physicalInstance_endpoint_reader_empty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level = p.levels)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    l.endpointReaderWalk p e ⊆ holes u :=
  l.physicalInstance_endpoint_reader_empty_of_closure p hl hM ha initial target e he
    (l.endpointReaderBlockers p hl hM ha e he)
    (l.endpointReaderBlockers_closure p hl hM ha initial target e he heM)
    (l.endpointReaderBlockers_guards p hl hM ha e he heM) hsu hut ht

/-- All three public long segments of every actual last-level endpoint stay empty. -/
theorem physicalInstance_deeperWalk_last_empty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    l.deeperWalkHoles p (p.levels - 1) ⊆ holes u := by
  intro q hq
  rcases Finset.mem_union.mp hq with hf | hw
  · exact l.physicalInstance_readerWalk_last_empty p hl hM ha initial target hsu hut ht
      (Finset.mem_union_left _ hf)
  obtain ⟨s, hs, hcontains⟩ := (SegmentRecipe.mem_holes _ q).mp hw
  obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨he, hgt⟩ := List.mem_filter.mp he
  have hgt : p.levels - 1 < e.level := of_decide_eq_true hgt
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have heM : e.level = p.levels := by omega
  have hwalks := l.endpointBaseSegments_subset_walks p hl hM e he
    ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hcontains⟩)
  exact (Finset.mem_union.mp hwalks).elim
    (fun h => l.physicalInstance_endpoint_publicWalk_empty p hl hM ha initial target e he heM hsu hut ht h)
    (fun h => l.physicalInstance_endpoint_reader_empty p hl hM ha initial target e he heM hsu hut ht h)

end PushPuzzle.PushS.PortLayout
