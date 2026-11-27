/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortEndpointInnerWall
import all PushS.PortEndpointOuterWalls
import all PushS.PortWideGeometry
import all PushS.PortCentralStrip

/-! Finite inner-wall families and actual outward guards of the r corridors. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

private def innerDepths (l : PortLayout) (p : Scales.Parameters) (e : Endpoint) : Finset ℕ :=
  (l.workingDepthCoordinates p).toFinset.filter fun v => v < readDepth p e.level

private theorem inner_depth_data (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (v : {v // v ∈ innerDepths l p e}) :
    v.val ∈ l.workingDepthCoordinates p ∧ v.val < readDepth p e.level := by
  have h := Finset.mem_filter.mp v.property
  exact ⟨List.mem_toFinset.mp h.1, h.2⟩

private noncomputable def innerSeparator (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) (v : {v // v ∈ innerDepths l p e}) :
    EndpointWideSeparator l p e v.val :=
  Classical.choice (l.endpointWideSeparator_before_nonempty p hl hM ha he
    (inner_depth_data l p e v).1 (inner_depth_data l p e v).2)

/-- The actual finite inner-wall family over every selected row shallower than the endpoint. -/
noncomputable def endpointInnerWalls (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  (innerDepths l p e).attach.biUnion fun v =>
    l.endpointInnerWall p e (innerSeparator l p hl hM ha e he v)

/-- Every cell of the complete inner-wall family is initially occupied at the last level. -/
theorem endpointInnerWalls_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level = p.levels) :
    l.endpointInnerWalls p hl hM ha e he ⊆
      (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  intro q hq
  obtain ⟨v, _, hq⟩ := Finset.mem_biUnion.mp hq
  exact l.endpointInnerWall_initial_full p hl hM ha initial target e he _
    (inner_depth_data l p e v).1 (inner_depth_data l p e v).2 heM hq

/-- The actual finite inner-wall family is anchored to the established page background. -/
theorem endpointInnerWalls_anchored (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) :
    Freeze.Anchored (l.endpointInnerWalls p hl hM ha e he) (l.pageFrozenBlockers p hl) := by
  apply Freeze.Anchored.biUnion
  intro v _
  exact l.endpointInnerWall_anchored p hl e _ (inner_depth_data l p e v).1

/-- One actual finite freezing closure adds the last-level endpoint's whole inner-wall family. -/
theorem endpointInnerWalls_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level = p.levels) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial (l.pageBlockers p hl)
      (l.endpointInnerWalls p hl hM ha e he ∪ l.pageFrozenBlockers p hl) := by
  have hc := Freeze.Closure.add (l.pageBackground_closure p hl hM ha initial target)
    (l.endpointInnerWalls_initial_full p hl hM ha initial target e he heM)
    (l.endpointInnerWalls_anchored p hl hM ha e he)
  have heq : (l.pageFrozenBlockers p hl ∪ l.endpointInnerWalls p hl hM ha e he :
      Finset (Cell (p.W + 1) (p.H + 1))) =
      l.endpointInnerWalls p hl hM ha e he ∪ l.pageFrozenBlockers p hl := Finset.union_comm _ _
  exact heq ▸ hc

/-- Every outward horizontal step from the actual r corridor at a selected shallower row
meets the same concrete inner-wall family or an established page blocker. -/
theorem endpointInnerWalls_guard (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints)
    {q r : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = EndpointStreet.r.column p e)
    (hy : q.2 ∈ l.workingRowSet p) (hf : q ∉ Boundary.frame)
    (hdepth : (if e.side = .upper then q.2.val else p.H - q.2.val) < readDepth p e.level)
    (hadj : Adjacent (if e.inward then .east else .west) q r) :
    r ∈ l.endpointInnerWalls p hl hM ha e he ∪ l.pageFrozenBlockers p hl := by
  have hmax := readDepth_le_last p e.level
  obtain ⟨v, hv, hrow⟩ := selected_depth l p e.side hy hf (by omega)
  have hpos := workingDepth_positive l p hv
  have hve : v < readDepth p e.level := by
    cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hrow hdepth <;> omega
  let v' : {v // v ∈ innerDepths l p e} :=
    ⟨v, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hv, hve⟩⟩
  have hg := l.endpointInnerWall_guard p hl e (innerSeparator l p hl hM ha e he v') hx hrow hadj
  rcases Finset.mem_union.mp hg with hw | hp
  · apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨v', Finset.mem_attach _ _, hw⟩
  · exact Finset.mem_union_right _ hp

end PushPuzzle.PushS.PortLayout
