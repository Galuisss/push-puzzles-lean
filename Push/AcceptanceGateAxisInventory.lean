/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateAxisNoInput
public import PushS.PortGateAxisInventory
public import PushS.PortRailProjection
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality
import all PushS.PortWalkBudget

/-! The actual gate-axis deficit counts its extra holes; a balanced terminal count restores the whole physical line dynamics. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) {g : Placement} (hg : g ∈ placements l)
  {kind : Shuttle.Kind} (hk : g.gate = some kind)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hg hk in
private theorem gate_axis_initial_card : (holes (I).initial ∩ gateAxis p (g.left + 1)).card = 4 := by
  have gate := placement_gate_mem l hg hk
  obtain ⟨upper, hu, hs, hp⟩ := l.endpoints_upper_exists hl (gate_middle_lt l hl gate)
  have initialHoles : (holes (I).initial : Finset (Cell (p.W + 1) (p.H + 1))) =
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p (l.canonical initial)) :=
    l.physicalInstance_initial_holes p hl hM haxes (l.canonical initial) (l.canonical target)
  exact (congrArg (fun E : Finset (Cell (p.W + 1) (p.H + 1)) => (E ∩ gateAxis p (g.left + 1)).card) initialHoles).trans
    (l.encodedSegments_gateAxis_card p hl hM haxes (l.canonical initial) hg hk hu hs hp)

include hgate hg hk

/-- Every actual gate middle axis has its original four holes plus its genuine box deficit. -/
theorem canonical_gateAxis_deficit_balance {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    (holes u ∩ gateAxis p (g.left + 1)).card =
      4 + (Inventory.count (gateAxis p (g.left + 1)) (I).initial - Inventory.count (gateAxis p (g.left + 1)) u) := by
  let R : Finset (Cell (p.W + 1) (p.H + 1)) := gateAxis p (g.left + 1)
  have hi := center_of_gate l (placement_gate_mem l hg hk)
  have mono := Inventory.reachable_mono
    (canonical_gateAxis_no_input_prefix l p hl hM haxes initial target hgate hi hsu hut accepted)
  have start := gate_axis_initial_card l p hl hM haxes initial target hg hk
  have ci := Inventory.count_add_holes R (I).initial
  have cu := Inventory.count_add_holes R u
  have balanced : Inventory.count R u + (holes u ∩ R).card = Inventory.count R (I).initial + 4 :=
    cu.trans (ci.symm.trans (congrArg (Inventory.count R (I).initial + ·) start))
  have initialTotal := Inventory.count_add_compl R (I).initial
  have currentTotal := Inventory.count_add_compl R u
  have total : Inventory.count R (I).initial + Inventory.count Rᶜ (I).initial = Inventory.count R u + Inventory.count Rᶜ u :=
    initialTotal.trans (hsu.card_boxes.symm.trans currentTotal.symm)
  change Inventory.count Rᶜ (I).initial ≤ Inventory.count Rᶜ u at mono
  change (holes u ∩ R).card = 4 + (Inventory.count R (I).initial - Inventory.count R u)
  omega

/-- A genuine four-hole terminal certificate fixes every earlier actual gate-axis hole count. -/
theorem canonical_gateAxis_holes_of_terminal {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (terminal : (holes t ∩ gateAxis p (g.left + 1)).card = 4) : (holes u ∩ gateAxis p (g.left + 1)).card = 4 := by
  have hi := center_of_gate l (placement_gate_mem l hg hk)
  exact Inventory.holes_of_balanced_compl
    (canonical_gateAxis_no_input_prefix l p hl hM haxes initial target hgate hi hsu hut accepted)
    (canonical_gateAxis_no_input_suffix l p hl hM haxes initial target hgate hi hsu hut accepted)
    (gate_axis_initial_card l p hl hM haxes initial target hg hk) terminal

/-- The actual gate-axis box inventory is preserved by each step once its terminal deficit vanishes. -/
theorem canonical_gateAxis_inventory_step_of_terminal {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (terminal : (holes t ∩ gateAxis p (g.left + 1)).card = 4) :
    Inventory.count (gateAxis p (g.left + 1)) u = Inventory.count (gateAxis p (g.left + 1)) v := by
  have before := canonical_gateAxis_holes_of_terminal l p hl hM haxes initial target hgate hg hk
    hsu ((Relation.ReflTransGen.single step).trans hvt) accepted terminal
  have after := canonical_gateAxis_holes_of_terminal l p hl hM haxes initial target hgate hg hk
    (hsu.tail step) hvt accepted terminal
  have cu := Inventory.count_add_holes (gateAxis p (g.left + 1)) u
  have cv := Inventory.count_add_holes (gateAxis p (g.left + 1)) v
  omega

/-- Every real push has the same source and destination membership in a terminal-balanced gate axis. -/
theorem canonical_gateAxis_transfer_iff_of_terminal {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (terminal : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    (run : Run (I).board d u n) (positive : 0 < n)
    (boxes : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1))) :
    run.cell 1 ∈ gateAxis p (g.left + 1) ↔ run.cell ⟨n + 1, by omega⟩ ∈ gateAxis p (g.left + 1) :=
  Inventory.transfer_iff_of_count run positive boxes
    (canonical_gateAxis_inventory_step_of_terminal l p hl hM haxes initial target hgate hg hk hsu step hvt accepted terminal)

/-- The balanced actual accepted prefix follows the original masked gate-axis line semantics. -/
theorem canonical_gateAxis_admissible_prefix_of_terminal {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (terminal : (holes t ∩ gateAxis p (g.left + 1)).card = 4) :
    Relation.ReflTransGen (RowLabels.LineAdmissible (I).board none .south (p.x (g.left + 1)))
      (BoxMask.keep (I).initial (gateAxis p (g.left + 1))) (BoxMask.keep u (gateAxis p (g.left + 1))) := by
  apply BoxMask.keep_admissible_reachable (gateAxis_runClosed p (g.left + 1)) ?_ ?_
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1
  · apply Path.enrich hsu
    intro a b hsa step hbu
    exact ⟨step, canonical_gateAxis_inventory_step_of_terminal l p hl hM haxes initial target hgate hg hk
      hsa step (hbu.trans hut) accepted terminal⟩

/-- The remainder of the same actual balanced trajectory has the same gate-axis line semantics. -/
theorem canonical_gateAxis_admissible_suffix_of_terminal {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (terminal : (holes t ∩ gateAxis p (g.left + 1)).card = 4) :
    Relation.ReflTransGen (RowLabels.LineAdmissible (I).board none .south (p.x (g.left + 1)))
      (BoxMask.keep u (gateAxis p (g.left + 1))) (BoxMask.keep t (gateAxis p (g.left + 1))) := by
  apply BoxMask.keep_admissible_reachable (gateAxis_runClosed p (g.left + 1)) ?_ ?_
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1
  · apply Path.enrich hut
    intro a b hua step hbt
    exact ⟨step, canonical_gateAxis_inventory_step_of_terminal l p hl hM haxes initial target hgate hg hk
      (hsu.trans hua) step hbt accepted terminal⟩

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
