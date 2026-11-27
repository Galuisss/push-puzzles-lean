/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortWireNoInput
public import PushS.InventoryHoles
import all PushS.PortBackground

/-! Exact storage targets close every actual ordinary WIRE's open-rail inventory. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- Every actual ordinary WIRE retains exactly its initial three holes at every successful prefix. -/
theorem physicalInstance_wireOpenRail_holes {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : (holes u ∩ wireOpenRail p g).card = 3 := by
  exact Inventory.holes_of_balanced_compl
    (l.physicalInstance_wire_no_input_prefix p hl hM ha initial target hg hw hsu hut ht)
    (l.physicalInstance_wire_no_input_suffix p hl hM ha initial target hg hw hsu hut ht)
    (l.physicalInstance_wireOpenRail_initial_holes p hl hM ha initial target hg hw)
    (l.physicalInstance_wireOpenRail_target_holes p hl hM ha initial target hg hw ht)

/-- A successful physical step preserves the open WIRE's box inventory. -/
theorem physicalInstance_wire_inventory_step {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    Inventory.count (wireOpenRail p g) u = Inventory.count (wireOpenRail p g) v := by
  have hu := l.physicalInstance_wireOpenRail_holes p hl hM ha initial target hg hw hsu
    ((Relation.ReflTransGen.single hm).trans hvt) ht
  have hv := l.physicalInstance_wireOpenRail_holes p hl hM ha initial target hg hw (hsu.tail hm) hvt ht
  have hcu := Inventory.count_add_holes (wireOpenRail p g) u
  have hcv := Inventory.count_add_holes (wireOpenRail p g) v
  omega

/-- First box and destination hole lie on the open WIRE together, for every actual successful push. -/
theorem physicalInstance_wire_transfer_iff {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    (run : Run (I).board d u n) (hn : 0 < n)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1))) :
    run.cell 1 ∈ wireOpenRail p g ↔ run.cell ⟨n + 1, by omega⟩ ∈ wireOpenRail p g := by
  have he := l.physicalInstance_wire_inventory_step p hl hM ha initial target hg hw hsu hm hvt ht
  exact Inventory.transfer_iff_of_count run hn hb he

/-- The identical physical prefix carries balanced open-rail inventories at every step. -/
theorem physicalInstance_wire_balanced_prefix {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (fun a b => Step (I).board none a b ∧
      Inventory.count (wireOpenRail p g) a = Inventory.count (wireOpenRail p g) b) (I).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact ⟨hm, l.physicalInstance_wire_inventory_step p hl hM ha initial target hg hw hsa hm (hbu.trans hut) ht⟩

end Solution
end PushPuzzle.PushS.PortLayout
