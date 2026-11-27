/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateNoInput
public import PushS.InventoryHoles
import all PushS.PortBackground

/-! Equal initial and exact-target inventories close the actual three-port horizontal rails. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- Every successful prefix keeps κ+11 holes on each actual three-port horizontal open rail. -/
theorem physicalInstance_gateOpenRail_holes {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : (holes u ∩ gateOpenRail p g).card = kind.kappa.toNat + 11 := by
  exact Inventory.holes_of_balanced_compl
    (l.physicalInstance_gateRail_no_input_prefix p hl hM ha initial target hg hk hsu hut ht)
    (l.physicalInstance_gateRail_no_input_suffix p hl hM ha initial target hg hk hsu hut ht)
    (l.physicalInstance_gateOpenRail_initial_holes p hl hM ha initial target hg hk)
    (l.physicalInstance_gateOpenRail_target_holes p hl hM ha initial target hg hk ht)

/-- Every successful physical step keeps the actual gate rail's box inventory. -/
theorem physicalInstance_gateRail_inventory_step {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    Inventory.count (gateOpenRail p g) u = Inventory.count (gateOpenRail p g) v := by
  have hbefore := l.physicalInstance_gateOpenRail_holes p hl hM ha initial target hg hk hsu
    ((Relation.ReflTransGen.single hm).trans hvt) ht
  have hafter := l.physicalInstance_gateOpenRail_holes p hl hM ha initial target hg hk (hsu.tail hm) hvt ht
  have hcu := Inventory.count_add_holes (gateOpenRail p g) u
  have hcv := Inventory.count_add_holes (gateOpenRail p g) v
  omega

/-- Every actual successful push has its first box and destination on the gate rail together. -/
theorem physicalInstance_gateRail_transfer_iff {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    (run : Run (I).board d u n) (hn : 0 < n)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1))) :
    run.cell 1 ∈ gateOpenRail p g ↔ run.cell ⟨n + 1, by omega⟩ ∈ gateOpenRail p g := by
  exact Inventory.transfer_iff_of_count run hn hb
    (l.physicalInstance_gateRail_inventory_step p hl hM ha initial target hg hk hsu hm hvt ht)

/-- The identical successful physical prefix has constant gate-rail inventory at every step. -/
theorem physicalInstance_gateRail_balanced_prefix {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (fun a b => Step (I).board none a b ∧
      Inventory.count (gateOpenRail p g) a = Inventory.count (gateOpenRail p g) b) (I).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact ⟨hm, l.physicalInstance_gateRail_inventory_step p hl hM ha initial target hg hk hsa hm (hbu.trans hut) ht⟩

end Solution
end PushPuzzle.PushS.PortLayout
