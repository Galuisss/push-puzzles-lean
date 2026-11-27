/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortOrdinaryWalks
import all PushS.PortEndpointReaderFreeze
import all PushS.PortEndpointLevelReader
import all PushS.PortBackground
import all PushS.PortPageBackground

/-! The actual ordinary reader closures guard every back neighbour throughout a solution. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- The computed reader closure on the endpoint's actual level. -/
noncomputable def endpointOrdinaryBlockers (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  if e.level = p.levels then l.endpointReaderBlockers p hl hM ha e he
  else l.endpointLevelReaderBlockers p hl hM ha e he

private noncomputable def ordinaryReaderBasis (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (e : Endpoint) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  if e.level = p.levels then l.pageBlockers p hl ∪ l.readerMidpointRows p p.levels
  else (l.pageBlockers p hl ∪ l.interlevelMarkers p e.level) ∪ l.readerMidpointRows p e.level

private theorem ordinaryReader_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial
      (ordinaryReaderBasis l p hl e) (l.endpointOrdinaryBlockers p hl hM ha e he) := by
  by_cases hlevel : e.level = p.levels
  · simp only [ordinaryReaderBasis, endpointOrdinaryBlockers, ite_eq_left hlevel]
    exact l.endpointReaderBlockers_closure p hl hM ha initial target e he hlevel
  · have hlt : e.level < p.levels := by
      have := (l.endpoints_level_bounds p hl hM he).2
      omega
    simp only [ordinaryReaderBasis, endpointOrdinaryBlockers, ite_eq_right hlevel]
    exact l.endpointLevelReaderBlockers_closure p hl hM ha initial target e he hlt

/-- Every selected outward axis neighbour through the endpoint's own work row lies in its closure. -/
theorem endpointOrdinaryBlockers_front_mem (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) {v : ℕ}
    (hv : v ∈ l.workingDepthCoordinates p) (hle : v ≤ readDepth p e.level)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = if e.inward then p.x e.port - 1 else p.x e.port + 1)
    (hy : q.2.val = if e.side = .upper then v else p.H - v) :
    q ∈ l.endpointOrdinaryBlockers p hl hM ha e he := by
  have hfront := l.endpointFrontRods_back_mem p hl hM e he hv hle hx hy
  unfold endpointOrdinaryBlockers
  split
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hfront))
  · exact Finset.mem_union_right _ hfront

/-- The cell behind the receiving column's work row lies in the same actual closure. -/
theorem endpointOrdinaryBlockers_cap_mem (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = EndpointStreet.r.column p e)
    (hy : q.2.val = if e.side = .upper then readDepth p e.level + 1
      else p.H - (readDepth p e.level + 1)) :
    q ∈ l.endpointOrdinaryBlockers p hl hM ha e he := by
  unfold endpointOrdinaryBlockers
  split
  · rename_i hlevel
    exact (l.endpointReaderBlockers_guards p hl hM ha e he hlevel).cap q hx hy
  · exact (l.endpointLevelReaderBlockers_guards p hl hM ha e he).cap q hx hy

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
  (e : Endpoint) (he : e ∈ l.endpoints)

local notation "I" => l.physicalInstance p hl hM ha initial target

include he

private theorem ordinaryReader_basis_step {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    Freeze.AvoidingStep (I).board none (ordinaryReaderBasis l p hl e) u v := by
  have hmidU := l.physicalInstance_allMidpointRows_excluded p hl hM ha initial target e.level
    hsu ((Relation.ReflTransGen.single hm).trans hvt) ht
  have hmidV := l.physicalInstance_allMidpointRows_excluded p hl hM ha initial target e.level
    (hsu.tail hm) hvt ht
  by_cases hlevel : e.level = p.levels
  · simp only [ordinaryReaderBasis, ite_eq_left hlevel]
    exact (step_page_avoiding l p hl hM ha initial target hsu hm hvt ht).union_excluded
      (hlevel ▸ hmidU) (hlevel ▸ hmidV)
  · have hbase := l.physicalInstance_interlevel_step_avoiding p hl hM ha initial target e.level
      (l.endpoints_level_bounds p hl hM he).1 hsu hm hvt ht
      (fun _ hs hst => l.physicalInstance_deeperWalk_empty p hl hM ha initial target e.level hs hst ht)
    simp only [ordinaryReaderBasis, ite_eq_right hlevel]
    exact hbase.union_excluded hmidU hmidV

private theorem ordinaryReader_basis_prefix {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (Freeze.AvoidingStep (I).board none (ordinaryReaderBasis l p hl e)) (I).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact ordinaryReader_basis_step l p hl hM ha initial target e he hsa hm (hbu.trans hut) ht

/-- Every actual successful prefix avoids the complete ordinary reader closure at every level. -/
theorem physicalInstance_ordinary_reader_avoiding_prefix {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (Freeze.AvoidingStep (I).board none
      (l.endpointOrdinaryBlockers p hl hM ha e he)) (I).initial u :=
  (ordinaryReader_closure l p hl hM ha initial target e he).reachable
    (ordinaryReader_basis_prefix l p hl hM ha initial target e he hsu hut ht)

/-- The next actual successful step avoids every box in that ordinary reader closure. -/
theorem physicalInstance_ordinary_reader_step_avoiding {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    Freeze.AvoidingStep (I).board none (l.endpointOrdinaryBlockers p hl hM ha e he) u v :=
  (ordinaryReader_closure l p hl hM ha initial target e he).step
    (ordinaryReader_basis_prefix l p hl hM ha initial target e he hsu
      ((Relation.ReflTransGen.single hm).trans hvt) ht)
    (ordinaryReader_basis_step l p hl hM ha initial target e he hsu hm hvt ht)

end Solution
end PushPuzzle.PushS.PortLayout
