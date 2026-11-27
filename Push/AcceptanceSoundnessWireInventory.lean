/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWireNoInput
public import PushS.InventoryHoles

/-! The actual one-way WIRE inventory starts with three holes and can only gain holes. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- No-input makes the number of actual open-rail holes monotone along every accepted suffix. -/
theorem canonical_wire_holes_mono {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (huv : Reachable (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    (PushS.holes u ∩ wireOpenRail p g).card ≤ (PushS.holes v ∩ wireOpenRail p g).card := by
  have hp : Relation.ReflTransGen (Inventory.ForwardStep (I).board none (wireOpenRail p g)ᶜ) u v := by
    apply Path.enrich huv
    intro a b hua hm hbv
    exact canonical_wire_no_input l p hl hM haxes initial target hgate hg hw (hsu.trans hua) hm (hbv.trans hvt) ha
  have hm : Inventory.count (wireOpenRail p g)ᶜ u ≤ Inventory.count (wireOpenRail p g)ᶜ v :=
    Inventory.reachable_mono hp
  have hcu := Inventory.count_add_compl (wireOpenRail p g) u
  have hcv := Inventory.count_add_compl (wireOpenRail p g) v
  have hhu := Inventory.count_add_holes (wireOpenRail p g) u
  have hhv := Inventory.count_add_holes (wireOpenRail p g) v
  have hcard : v.boxes.card = u.boxes.card := huv.card_boxes
  change Inventory.count (wireOpenRail p g) u + Inventory.count (wireOpenRail p g)ᶜ u = u.boxes.card at hcu
  change Inventory.count (wireOpenRail p g) v + Inventory.count (wireOpenRail p g)ᶜ v = v.boxes.card at hcv
  omega

/-- Every actual ordinary rail has at least its three initial holes throughout an accepted trajectory. -/
theorem canonical_wire_holes_ge_three {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    3 ≤ (PushS.holes u ∩ wireOpenRail p g).card := by
  have hm := canonical_wire_holes_mono l p hl hM haxes initial target hgate hg hw .refl hsu hut ha
  have hi := l.physicalInstance_wireOpenRail_initial_holes p hl hM haxes
    (l.canonical initial) (l.canonical target) hg hw
  exact hi ▸ hm

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
