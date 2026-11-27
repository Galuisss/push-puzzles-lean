/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import Push.AcceptanceSoundnessWireRowInventory
public import PushS.InventoryHoles
import all PushS.PortBackground

/-! Actual full-row quotas close every ordinary WIRE inventory along the same physical path. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness


open PushFS PushS PushS.PortLayout AcceptanceProgram

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- Every actual ordinary WIRE retains exactly its initial three holes at every successful prefix. -/
theorem canonical_wireOpenRail_holes {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) : (holes u ∩ wireOpenRail p g).card = 3 := by
  exact Inventory.holes_of_balanced_compl
    (canonical_wire_no_input_prefix l p hl hM haxes initial target hgate hg hw hsu hut ha)
    (canonical_wire_no_input_suffix l p hl hM haxes initial target hgate hg hw hsu hut ha)
    (l.physicalInstance_wireOpenRail_initial_holes p hl hM haxes (l.canonical initial) (l.canonical target) hg hw)
    (canonical_wire_terminal_holes l p hl hM haxes initial target hgate hg hw (hsu.trans hut) ha)

/-- A successful physical step preserves the open WIRE's box inventory. -/
theorem canonical_wire_inventory_step {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Inventory.count (wireOpenRail p g) u = Inventory.count (wireOpenRail p g) v := by
  have hu := canonical_wireOpenRail_holes l p hl hM haxes initial target hgate hg hw hsu
    ((Relation.ReflTransGen.single hm).trans hvt) ha
  have hv := canonical_wireOpenRail_holes l p hl hM haxes initial target hgate hg hw (hsu.tail hm) hvt ha
  have hcu := Inventory.count_add_holes (wireOpenRail p g) u
  have hcv := Inventory.count_add_holes (wireOpenRail p g) v
  omega

/-- First box and destination hole lie on the open WIRE together, for every actual successful push. -/
theorem canonical_wire_transfer_iff {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (run : Run (I).board d u n) (hn : 0 < n)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1))) :
    run.cell 1 ∈ wireOpenRail p g ↔ run.cell ⟨n + 1, by omega⟩ ∈ wireOpenRail p g := by
  have he := canonical_wire_inventory_step l p hl hM haxes initial target hgate hg hw hsu hm hvt ha
  exact Inventory.transfer_iff_of_count run hn hb he

/-- The identical physical prefix carries balanced open-rail inventories at every step. -/
theorem canonical_wire_balanced_prefix {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Relation.ReflTransGen (fun a b => Step (I).board none a b ∧
      Inventory.count (wireOpenRail p g) a = Inventory.count (wireOpenRail p g) b) (I).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact ⟨hm, canonical_wire_inventory_step l p hl hM haxes initial target hgate hg hw hsa hm (hbu.trans hut) ha⟩

end Solution
end PushPuzzle.Push.AcceptanceSoundness
