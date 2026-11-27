/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateAxisNoInput
public import PushS.InventoryHoles
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality
import all PushS.PortWalkBudget
import all PushS.PortBackground

/-! The exact four-hole target closes the actual middle-axis inventory at every successful prefix. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- Every successful prefix retains four holes on each actual gate middle-axis open segment. -/
theorem physicalInstance_gateAxis_holes {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : (holes u ∩ gateAxis p (g.left + 1)).card = 4 := by
  have hgate := placement_gate_mem l hg hk
  have hi := center_of_gate l hgate
  obtain ⟨upper, hu, hs, hp⟩ := l.endpoints_upper_exists hl (gate_middle_lt l hl hgate)
  apply Inventory.holes_of_balanced_compl (w := p.W + 1) (h := p.H + 1)
    (l.physicalInstance_gateAxis_no_input_prefix p hl hM ha initial target hi hsu hut ht)
    (l.physicalInstance_gateAxis_no_input_suffix p hl hM ha initial target hi hsu hut ht)
  · have hinit : holes ((I).initial : State (p.W + 1) (p.H + 1)) =
        SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial) :=
      l.physicalInstance_initial_holes p hl hM ha initial target
    exact hinit.symm ▸ l.encodedSegments_gateAxis_card p hl hM ha initial hg hk hu hs hp
  · have hgoal : holes t = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target) := by
      change (t.boxes : Finset (Cell (p.W + 1) (p.H + 1)))ᶜ = _
      rw [ht]
      exact l.physicalInstance_goal_holes p hl hM ha initial target
    rw [hgoal]
    exact l.encodedSegments_gateAxis_card p hl hM ha target hg hk hu hs hp

/-- The actual gate middle-axis box count is unchanged by each successful step. -/
theorem physicalInstance_gateAxis_inventory_step {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    Inventory.count (gateAxis p (g.left + 1)) u = Inventory.count (gateAxis p (g.left + 1)) v := by
  have hbefore := l.physicalInstance_gateAxis_holes p hl hM ha initial target hg hk hsu
    ((Relation.ReflTransGen.single hm).trans hvt) ht
  have hafter := l.physicalInstance_gateAxis_holes p hl hM ha initial target hg hk (hsu.tail hm) hvt ht
  have hcu := Inventory.count_add_holes (gateAxis p (g.left + 1)) u
  have hcv := Inventory.count_add_holes (gateAxis p (g.left + 1)) v
  omega

/-- A successful complete push never transfers a box across the actual middle-axis boundary. -/
theorem physicalInstance_gateAxis_transfer_iff {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    (run : Run (I).board d u n) (hn : 0 < n)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1))) :
    run.cell 1 ∈ gateAxis p (g.left + 1) ↔ run.cell ⟨n + 1, by omega⟩ ∈ gateAxis p (g.left + 1) := by
  exact Inventory.transfer_iff_of_count run hn hb
    (l.physicalInstance_gateAxis_inventory_step p hl hM ha initial target hg hk hsu hm hvt ht)

/-- The complete actual prefix has constant gate middle-axis inventory at every step. -/
theorem physicalInstance_gateAxis_balanced_prefix {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (fun a b => Step (I).board none a b ∧
      Inventory.count (gateAxis p (g.left + 1)) a = Inventory.count (gateAxis p (g.left + 1)) b) (I).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact ⟨hm, l.physicalInstance_gateAxis_inventory_step p hl hM ha initial target hg hk hsa hm (hbu.trans hut) ht⟩

end Solution
end PushPuzzle.PushS.PortLayout
