/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import Push.AcceptanceGateRailNoInput
public import PushS.InventoryHoles
import all PushS.PortBackground

/-! Actual balanced terminal rail inventories close the same accepted physical gate trajectory. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness


open PushFS PushS PushS.PortLayout AcceptanceProgram

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- Every successful prefix keeps κ+11 holes on each actual three-port horizontal open rail. -/
private theorem canonical_gateOpenRail_holes_of_terminal {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    (railInventory : (holes t ∩ gateOpenRail p g).card = kind.kappa.toNat + 11) : (holes u ∩ gateOpenRail p g).card = kind.kappa.toNat + 11 := by
  exact Inventory.holes_of_balanced_compl
    (canonical_gateRail_no_input_prefix_of_axis_inventory l p hl hM haxes initial target hgate hg hk hsu hut accepted axisInventory)
    (canonical_gateRail_no_input_suffix_of_axis_inventory l p hl hM haxes initial target hgate hg hk hsu hut accepted axisInventory)
    (l.physicalInstance_gateOpenRail_initial_holes p hl hM haxes (l.canonical initial) (l.canonical target) hg hk)
    railInventory

/-- Every successful physical step keeps the actual gate rail's box inventory. -/
theorem canonical_gateRail_inventory_step_of_terminal {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    (railInventory : (holes t ∩ gateOpenRail p g).card = kind.kappa.toNat + 11) :
    Inventory.count (gateOpenRail p g) u = Inventory.count (gateOpenRail p g) v := by
  have hbefore := canonical_gateOpenRail_holes_of_terminal l p hl hM haxes initial target hgate hg hk hsu
    ((Relation.ReflTransGen.single hm).trans hvt) accepted axisInventory railInventory
  have hafter := canonical_gateOpenRail_holes_of_terminal l p hl hM haxes initial target hgate hg hk (hsu.tail hm) hvt accepted axisInventory railInventory
  have hcu := Inventory.count_add_holes (gateOpenRail p g) u
  have hcv := Inventory.count_add_holes (gateOpenRail p g) v
  omega

/-- The identical successful physical prefix has constant gate-rail inventory at every step. -/
theorem canonical_gateRail_balanced_prefix_of_terminal {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    (railInventory : (holes t ∩ gateOpenRail p g).card = kind.kappa.toNat + 11) :
    Relation.ReflTransGen (fun a b => Step (I).board none a b ∧
      Inventory.count (gateOpenRail p g) a = Inventory.count (gateOpenRail p g) b) (I).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact ⟨hm, canonical_gateRail_inventory_step_of_terminal l p hl hM haxes initial target hgate hg hk hsa hm (hbu.trans hut) accepted axisInventory railInventory⟩

end Solution
end PushPuzzle.Push.AcceptanceSoundness
