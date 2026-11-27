/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointTail
import all PushS.PortEndpointOuterWalls
import all PushS.PortEndpointFStock
import all PushS.PortWideGeometry
import all PushS.PortCentralStrip
import all PushS.PortPageBackground
import all PushS.PortBackground

/-! The f-corridor inventory argument at every descending level. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

private noncomputable def levelOuterDepths (l : PortLayout) (p : Scales.Parameters) (e : Endpoint) :
    Finset ℕ := (l.workingDepthCoordinates p).toFinset.filter fun v => v ≤ readDepth p e.level + 2

private theorem level_outer_depth_data (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (v : {v // v ∈ levelOuterDepths l p e}) :
    v.val ∈ l.workingDepthCoordinates p ∧ v.val ≤ readDepth p e.level + 2 := by
  have h := Finset.mem_filter.mp v.property
  exact ⟨List.mem_toFinset.mp h.1, h.2⟩

private noncomputable def levelOuterSeparator (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) (v : {v // v ∈ levelOuterDepths l p e}) :
    EndpointOuterWideSeparator l p e v.val :=
  Classical.choice (l.endpointOuterWideSeparator_nonempty p hl hM ha he
    (level_outer_depth_data l p e v).1 (level_outer_depth_data l p e v).2)

/-- The actual outer-wall family through this endpoint's own branch row. -/
noncomputable def endpointLevelOuterWalls (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  (levelOuterDepths l p e).attach.biUnion fun v =>
    l.endpointOuterWall p e (levelOuterSeparator l p hl hM ha e he v)

/-- Every selected outer row of an arbitrary-level actual endpoint is initially full. -/
theorem endpointLevelOuterWalls_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) :
    l.endpointLevelOuterWalls p hl hM ha e he ⊆
      (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  intro q hq
  obtain ⟨v, _, hq⟩ := Finset.mem_biUnion.mp hq
  exact l.endpointOuterWall_initial_full_general p hl hM ha initial target e he _
    (level_outer_depth_data l p e v).1 hq

/-- All computed outer rows share the proved page-background anchors. -/
theorem endpointLevelOuterWalls_anchored (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) :
    Freeze.Anchored (l.endpointLevelOuterWalls p hl hM ha e he) (l.pageFrozenBlockers p hl) := by
  apply Freeze.Anchored.biUnion
  intro v _
  exact l.endpointOuterWall_anchored p hl e _ (level_outer_depth_data l p e v).1

/-- Each selected outward f neighbour meets the computed finite wall family. -/
theorem endpointLevelOuterWalls_guard (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) {q r : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = EndpointStreet.f.column p e) (hy : q.2 ∈ l.workingRowSet p)
    (hf : q ∉ Boundary.frame)
    (hdepth : (if e.side = .upper then q.2.val else p.H - q.2.val) ≤ readDepth p e.level + 2)
    (hadj : Adjacent (if e.inward then .west else .east) q r) :
    r ∈ l.endpointLevelOuterWalls p hl hM ha e he ∪ l.pageFrozenBlockers p hl := by
  have hmax := readDepth_le_last p e.level
  obtain ⟨v, hv, hrow⟩ := selected_depth l p e.side hy hf (by omega)
  have hvH := (workingDepth_positive l p hv).2
  have hve : v ≤ readDepth p e.level + 2 := by
    cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hrow hdepth <;> omega
  let v' : {v // v ∈ levelOuterDepths l p e} :=
    ⟨v, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hv, hve⟩⟩
  have hg := l.endpointOuterWall_guard p hl e (levelOuterSeparator l p hl hM ha e he v') hx hrow hadj
  rcases Finset.mem_union.mp hg with hw | hp
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨v', Finset.mem_attach _ _, hw⟩)
  · exact Finset.mem_union_right _ hp

/-- The actual tail and outside wall family protecting an endpoint's f inventory. -/
noncomputable def endpointFBlockers (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  ((l.pageFrozenBlockers p hl ∪ l.interlevelMarkers p e.level) ∪ endpointTail p e .f) ∪
    l.endpointLevelOuterWalls p hl hM ha e he

/-- The actual column tail followed by the actual outer rows gives the f-inventory closure. -/
theorem endpointFBlockers_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level < p.levels) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial
      (l.pageBlockers p hl ∪ l.interlevelMarkers p e.level) (l.endpointFBlockers p hl hM ha e he) := by
  have hanchor : Freeze.Anchored (l.endpointLevelOuterWalls p hl hM ha e he)
      ((l.pageFrozenBlockers p hl ∪ l.interlevelMarkers p e.level) ∪ endpointTail p e .f) :=
    (l.endpointLevelOuterWalls_anchored p hl hM ha e he).mono_blockers
      (fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h))
  exact .add (l.endpointTail_closure p hl hM ha initial target e he heM .f)
    (l.endpointLevelOuterWalls_initial_full p hl hM ha initial target e he) hanchor

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
  (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level < p.levels)

include he heM

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- Once the deeper public walks are empty, no actual step exports an f-corridor box. -/
theorem physicalInstance_level_fwalk_forward {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    (hP : ∀ s, Reachable (I).board none (I).initial s → Reachable (I).board none s t →
      l.deeperWalkHoles p e.level ⊆ holes s) :
    Inventory.ForwardStep (I).board none (endpointFWalk p e) u v := by
  have hut := (Relation.ReflTransGen.single hm).trans hvt
  have hj := (l.endpoints_level_bounds p hl hM he).1
  have hpre := l.physicalInstance_interlevel_avoiding_prefix p hl hM ha initial target e.level hj hsu hut ht hP
  have hstep := l.physicalInstance_interlevel_step_avoiding p hl hM ha initial target e.level hj hsu hm hvt ht hP
  have hguard := (l.endpointFBlockers_closure p hl hM ha initial target e he heM).step hpre hstep
  have hframe : Disjoint u.boxes Boundary.frame := by
    apply Finset.disjoint_left.mpr
    intro q hb hf
    exact (mem_holes _).mp (l.physicalInstance_readerWalk_last_empty p hl hM ha initial target
      hsu hut ht (Finset.mem_union_left _ hf)) hb
  apply fwalk_forward l p hl ha e he ?_ ?_ hguard hframe
    (l.physicalInstance_player_on_streets p hl hM ha initial target hsu hut ht)
    (l.physicalInstance_player_on_streets p hl hM ha initial target (hsu.tail hm) hvt ht)
  · intro q hq hf hy r hadj
    have hq' := (mem_endpointFWalk_iff p e q).mp hq
    have hqH := q.2.isLt
    have hY := readDepth_add_lt_H p e.level
    have hdepth : (if e.side = .upper then q.2.val else p.H - q.2.val) ≤ readDepth p e.level + 2 := by
      cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hq' ⊢ <;> omega
    have hg := l.endpointLevelOuterWalls_guard p hl hM ha e he hq'.1 hy hf hdepth hadj
    rcases Finset.mem_union.mp hg with hw | hp
    · exact Finset.mem_union_right _ hw
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hp))
  · intro q hx hy
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (l.endpointTail_start_mem p hl hM e he heM .f hx hy))

/-- Clearing the deeper actual public walks forces this level's complete f corridor empty
at every prefix of the same successful physical play. -/
theorem physicalInstance_level_fwalk_empty {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals)
    (hP : ∀ s, Reachable (I).board none (I).initial s → Reachable (I).board none s t →
      l.deeperWalkHoles p e.level ⊆ holes s) : endpointFWalk p e ⊆ holes u := by
  have hr : Relation.ReflTransGen (Inventory.ForwardStep (I).board none (endpointFWalk p e)) u t := by
    apply enrich_path hut
    intro a b hua hm hbt
    exact l.physicalInstance_level_fwalk_forward p hl hM ha initial target e he heM
      (hsu.trans hua) hm hbt ht hP
  exact fwalk_empty_of_forward l p hl hM ha initial target e he hr ht

end Solution
end PushPuzzle.PushS.PortLayout
