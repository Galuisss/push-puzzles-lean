/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGatePrivateWalk
import all PushS.PortBackground
import all PushS.PortPageBackground

/-! The actual gate private closure also guards each next successful physical step. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

private theorem gate_basis_step {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    Freeze.AvoidingStep (I).board none
      ((l.pageBlockers p hl ∪ l.gateInterlevelMarkers p) ∪ l.gateHalfMarkers p) u v := by
  have hut := (Relation.ReflTransGen.single hm).trans hvt
  exact ((step_page_avoiding l p hl hM ha initial target hsu hm hvt ht).union_excluded
    (l.physicalInstance_gate_interlevel_excluded p hl hM ha initial target hsu hut ht)
    (l.physicalInstance_gate_interlevel_excluded p hl hM ha initial target (hsu.tail hm) hvt ht)).union_excluded
      (l.physicalInstance_gate_halfMarkers_excluded p hl hM ha initial target hsu hut ht)
      (l.physicalInstance_gate_halfMarkers_excluded p hl hM ha initial target (hsu.tail hm) hvt ht)

/-- The established private closure guards the complete ray of each actual next successful push. -/
theorem physicalInstance_gate_private_step_avoiding {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    Freeze.AvoidingStep (I).board none (l.gatePrivateBlockers p hl hM ha hi) u v := by
  apply (l.gatePrivateBlockers_closure p hl hM ha initial target hi).step ?_
    (gate_basis_step l p hl hM ha initial target hsu hm hvt ht)
  apply enrich_path hsu
  intro a b hsa hab hbu
  exact gate_basis_step l p hl hM ha initial target hsa hab
    (hbu.trans ((Relation.ReflTransGen.single hm).trans hvt)) ht

end Solution
end PushPuzzle.PushS.PortLayout
